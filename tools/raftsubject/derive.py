#!/usr/bin/env python3
"""derive.py — mechanically derive the vendored raft SUBJECT TREE from deps/raft.

This is the re-runnable derivation required by the 2026-08-19 raftpb RULING
(docs/2026-08-15_raft-push-p0-scoping.md §8.6): the `plainpb` shim is not
hand-written, it is DERIVED BY STRIPPING the actual generated raftpb file, so
the delta re-derives when the `deps/raft` pin moves.

    tools/raftsubject/derive.py                 # write raftsubject/
    tools/raftsubject/derive.py --check         # derive to a temp dir, diff
    tools/raftsubject/derive.py --print-digests # emit the upstream digest table

WHY A SCRIPT AND NOT A CHECKED-IN HAND EDIT.  The subject tree is the thing we
verify.  A hand-written shim drifts silently from the library it claims to
stand for; a derivation refuses to run when the upstream file it strips has
changed shape.  Every rule below is keyed to a RECOGNISED declaration form, and
anything unrecognised REFUSES (see `refuse`) rather than being passed through
or dropped.  That is the whole point: a new protoc-gen-go release, or a new
raft rev, must be READ by a human before the tree moves.

THE THREE DERIVATION MODES

  verbatim  Copy, rewriting `go.etcd.io/raft/v3/<pkg>` import paths to the
            short dot-free form `<pkg>` (the frontend's case-relative
            multi-package convention, docs/2026-08-18_multipackage-identity.md
            §4/§6).  NOTHING else changes — in particular the frontier
            refusals (statement-position `copy`, `fmt.Sprintf` in a panic,
            the `String`/`Describe` rendering methods) are kept EXACTLY as
            upstream writes them, so they show up as honest reds instead of
            being papered over by a subject delta.

  plainpb   raftpb/raft.pb.go: strip the protobuf runtime out of the generated
            file, keeping the WIRE TYPES DECLARED (structs, field numbers in
            their struct tags, enums, getters) and turning every
            runtime-touching method into a FAIL-CLOSED STUB.  Additionally
            EMIT plain-Go deep-clone and structural-equality methods, derived
            from the same parsed field lists (raftpb's own confstate.go needs
            them; they carry a differential obligation — see the log).

  overlay   A hand-written replacement for an upstream file that cannot be
            mechanically stripped (it is hand-written Go that calls into the
            protobuf runtime).  Two raftpb files use it; logger.go no longer
            does (W4.2 retired the D-5 no-op overlay — the file is verbatim
            plus the recorded D-12 initializer patch, per the Q2 ruling).
            The upstream file's SHA-256 is PINNED here: when the
            pin moves and upstream changes, the derivation FAILS LOUD and the
            overlay must be revisited by hand.  That digest pin is the
            re-derivation contract for the files a script cannot derive.

  select    (W2.2) Keep a NAMED SET of top-level declarations from an upstream
            file VERBATIM and drop the rest, dropping named imports with them.
            One file uses it: node.go, whose type declarations (Ready,
            SoftState, Peer, IsEmptySnap, ...) RawNode needs and whose `node`
            goroutine loop — `context`, channels, the whole Node API — the
            plan of record excludes (master plan §W2.2: "RawNode-driven node
            loops (no node.go / context / time)").  The kept text is
            byte-verbatim per declaration; the DROPPED set is the delta, and
            it is enumerated in the ledger.  Fail-closed both ways: a named
            declaration that is not found refuses, and so does a dropped
            import whose name still appears in the kept text.

FAIL-CLOSED POSTURE.  Refusals are `sys.exit(2)` with the offending
declaration printed.  There is deliberately no `--force` and no
`--update-digests`: refreshing the pin is a human act (`--print-digests`
prints the table to paste, so the diff is visible in review).
"""

import argparse
import filecmp
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

# ---------------------------------------------------------------- the pin ----

# deps/raft rev this derivation was READ against.  A different rev is not
# automatically wrong, but it is unread: the digest table below is the actual
# gate, and this is the human-legible half of it.
PINNED_RAFT_REV = "56e32004b1af3a4cb625fbfe5dbca24fb6023d09"

# The node.go declarations RawNode needs, and NOTHING else (mode `select`).
# Everything omitted is the `node` implementation — the Node interface, the
# goroutine loop, StartNode/RestartNode and their `context` plumbing — which
# the plan of record replaces with a machine-side harness loop.
NODE_KEEP = [
    "$package", "$imports",
    "SnapshotStatus", "const(SnapshotFinish)", "var(emptyState)",
    "SoftState", "SoftState.equal", "Ready",
    "isHardStateEqual", "IsEmptyHardState", "IsEmptySnap",
    "Peer", "confChangeToMsg",
]
# Imports dropped with them; the derivation refuses if the kept text still
# names one.
NODE_DROP_IMPORTS = ["context"]

# The protobuf-runtime functions the vendored tree calls.  `derive.py` emits a
# subject-local `proto` package declaring exactly these, and REFUSES if the
# tree reaches for one that is not here — so a raft rev that starts calling
# `proto.Merge` cannot slip through.
#
# Since W4.1 (H-1 discharged, docs/raft-w41-log.md item 1) the four bodies are
# REAL: type-switch dispatch over the nine plainpb message types into the
# generated per-type codec (`raftpb/plain_codec.go` — AppendMessage /
# SizeMessage / UnmarshalMessage, derived from the same parsed field lists as
# CloneMessage).  A message type outside the nine still fails closed with an
# explicit panic in the dispatch default.
PROTO_FUNCS = {
    "Clone": ("func Clone(m Message) Message", "Message"),
    "Marshal": ("func Marshal(m Message) ([]byte, error)", "([]byte, error)"),
    "Unmarshal": ("func Unmarshal(b []byte, m Message) error", "error"),
    "Size": ("func Size(m Message) int", "int"),
}
PROTO_PATH = "google.golang.org/protobuf/proto"

# Upstream files -> (out path, mode).  Order is the emission order.
VENDOR = [
    ("raftpb/raft.pb.go", "raftpb/raft.pb.go", "plainpb"),
    ("raftpb/alias.go", "raftpb/alias.go", "verbatim"),
    ("raftpb/util.go", "raftpb/util.go", "verbatim"),
    ("raftpb/confstate.go", "raftpb/confstate.go", "overlay"),
    ("raftpb/confchange.go", "raftpb/confchange.go", "overlay"),
    ("quorum/quorum.go", "quorum/quorum.go", "verbatim"),
    ("quorum/majority.go", "quorum/majority.go", "verbatim"),
    ("quorum/joint.go", "quorum/joint.go", "verbatim"),
    ("quorum/voteresult_string.go", "quorum/voteresult_string.go", "verbatim"),
    ("tracker/inflights.go", "tracker/inflights.go", "verbatim"),
    ("tracker/progress.go", "tracker/progress.go", "verbatim"),
    ("tracker/state.go", "tracker/state.go", "verbatim"),
    ("tracker/tracker.go", "tracker/tracker.go", "verbatim"),
    # W4.2: upstream VERBATIM (the Q2 ruling; D-5's no-op overlay is RETIRED)
    # modulo the recorded D-12 initializer patch — see SUBJECT_PATCHES.
    ("logger.go", "raft/logger.go", "verbatim"),
    # W2.2: the raft ROOT package, scoped to what RawNode's decision paths
    # need.  node.go arrives as a declaration subset (mode `select`); the
    # `with_tla` variant of the tracing file is not vendored (the default
    # build takes state_trace_nop.go, and vendoring both would redeclare
    # every trace function — go/parser does not apply build constraints).
    ("confchange/confchange.go", "confchange/confchange.go", "verbatim"),
    ("confchange/restore.go", "confchange/restore.go", "verbatim"),
    ("bootstrap.go", "raft/bootstrap.go", "verbatim"),
    ("log.go", "raft/log.go", "verbatim"),
    ("log_unstable.go", "raft/log_unstable.go", "verbatim"),
    ("node.go", "raft/node_decls.go", "select"),
    ("raft.go", "raft/raft.go", "verbatim"),
    ("rawnode.go", "raft/rawnode.go", "verbatim"),
    ("read_only.go", "raft/read_only.go", "verbatim"),
    ("state_trace_nop.go", "raft/state_trace_nop.go", "verbatim"),
    ("status.go", "raft/status.go", "verbatim"),
    ("storage.go", "raft/storage.go", "verbatim"),
    ("types.go", "raft/types.go", "verbatim"),
    ("util.go", "raft/util.go", "verbatim"),
]

# SHA-256 of each upstream file at PINNED_RAFT_REV.  ANY change trips the
# derivation.  For `verbatim` files that is a courtesy (the rewrite is
# mechanical and would still work); for `plainpb` and `overlay` it is the
# contract — the rules and the hand-written replacements were written against
# exactly these bytes.
DIGESTS = {
    "raftpb/raft.pb.go": "d94c220250d54147f849f7c416787be4971903b4c95d93570e7906041513ff99",
    "raftpb/alias.go": "cf30bf89bdc663381fe1cedb7600ee8a8e6eeb2eac66fbaa39b612adcb19721a",
    "raftpb/util.go": "acdf57a935b4a011c32519c6efe236a352f906423651deaea422d269a9a2ac1f",
    "raftpb/confstate.go": "834b784909b8789e26f163b5879e9c282858e0392a68c9853998635fedf56240",
    "raftpb/confchange.go": "0d40cf8a7f45e0791bd1c287e7b7de99a3a814418d40ecee1be4cbee7a02876b",
    "quorum/quorum.go": "63d6aa6b319b49b16afc3d741cf57dc41a040637d66001f8477f4e90f6a61331",
    "quorum/majority.go": "dbe87c11688eddab3a44c047356c3696fc5e835be19bcb7771e4cbe631e16ea0",
    "quorum/joint.go": "974987a423a79d06014a562543507375377a25a24abe39265df9ef0819b68d49",
    "quorum/voteresult_string.go": "10c458e638369f50c5e7da0e05bc5468c1976c73bba022a0c6cd6703570e2f6b",
    "tracker/inflights.go": "4c1302b2c1937baf93c49e2265528a7b61184af8f3b3bbd1596b80c346e887a8",
    "tracker/progress.go": "1062711d8f2693bc56d14bdb73cac71f9a4cb041f00b09253948e422f4027eed",
    "tracker/state.go": "b4a19e82ddc422d15fb6cfa2738c16abe42cdf14166bc788d8fd536d79652fe8",
    "tracker/tracker.go": "1ffda5213765af23030c9a7b640478ff69c070231307adcd2bc9ecac6675d452",
    "logger.go": "bcf4b575b30d51d21956213dbc6d455fc8687c89cd45eab6f84f80dd9384a00b",
    "confchange/confchange.go": "b4e082d86bb67bff630a5f1465d5fedf794a6806d47bd420c705b9de8291d6b3",
    "confchange/restore.go": "744a5f97b4a9cc7d561ef96a155f8759102fa6553b651cff4f6901dada2007d1",
    "bootstrap.go": "92dee0b87b8a9ab0239514b3bb2e6c562b5be39645a5d4a7e575584179d40998",
    "log.go": "58316f5ae5a7e02067f83b9715af04ad375e1ba3e96f89ccd166e5cf947544d2",
    "log_unstable.go": "668447df175bba1ce5e5c2579b290844f9603631b5ce3de226758b62dca596e7",
    "node.go": "311ece789019299836c97ca24908a52ca0e96ea11d3c81109444b41f625607a9",
    "raft.go": "d3d8fa573e1488e3aa35b9b997ba943454f3f357740a550d4bcc44d81975f07f",
    "rawnode.go": "531cac8b286fd6e0bcd430c12053590325b9b00d113a584b8d3e6d1314c50f05",
    "read_only.go": "7277fd552348bee2dcc7f9afe8ce24860f35bb9693b64d293b3d343ca38d669a",
    "state_trace_nop.go": "0f358917d5769791c312811b5a30fca23fb0e2973f0439582ce1983d215bd2fb",
    "status.go": "67cea0e18c32d29f7b6f65e3d3450d4e92ee6e6cb3961122a7a2863eccd24c59",
    "storage.go": "22020183114fe7555bc44ebda1b5b0d67de6534b0c8735c08c8667a0bd245403",
    "types.go": "60068200885b00bbaff3daa09d468db89473c61c2150867f33d90ccfe16b438f",
    "util.go": "b85b6fd2915e7d09eb534df528c4ede99890ec3770b60b2ff75a69f2ad17b33e",
}

# ---- recorded subject patches (H-15, the election-jitter CHOICE SITE) ----
#
# W4.1 item 3 (docs/raft-w41-log.md; the ruling: docs/raft-w3-log.md H-15,
# harness design §5): the jitter draw is NONDETERMINISM and belongs to the
# ENVELOPE — `crypto/rand` + `math/big` are never modeled. The subject
# carries ONE recorded patch: `(*lockedRand).Intn`'s body becomes a plain-Go
# draw whose nondeterminism ENVELOPE under the machine is exactly [0, n) —
# the first key produced by ranging over a fresh n-key map, which is the
# machine's map-iteration choice site (and, under `go run`, Go's own
# randomized iteration order). `resetRandomizedElectionTimeout` then
# realizes raft's contract range [electionTimeout, 2*electionTimeout),
# which is what the latitude entry files (W4.5). Upstream itself treats
# the value as injectable (rafttest's set-randomized-election-timeout).
#
# The patch is keyed to upstream's EXACT text and fails closed on drift —
# a new rev's Intn must be re-read, not silently re-patched. Subject-delta
# ledger row: D-11 (the W4.1 log).
INTN_UPSTREAM = """func (r *lockedRand) Intn(n int) int {
	r.mu.Lock()
	v, _ := rand.Int(rand.Reader, big.NewInt(int64(n)))
	r.mu.Unlock()
	return int(v.Int64())
}"""

INTN_PATCHED = """// GOLEAN SUBJECT DELTA D-11 (H-15, the election-jitter CHOICE SITE —
// docs/raft-w41-log.md item 3). Upstream draws via crypto/rand +
// math/big, which the machine never models (jitter is nondeterminism;
// the envelope, not a stream of modeled bits, is the semantics). The
// draw below has envelope [0, n) on BOTH oracles: under the machine the
// first key of a map range is the map-iteration choice site; under
// `go run` it is Go's own randomized iteration order. The n <= 0 panic
// preserves upstream's failure mode (the upstream draw panics on a
// non-positive max). The mutex stays: globalRand is shared package
// state and dropping the lock would smuggle in a concurrency delta.
func (r *lockedRand) Intn(n int) int {
	if n <= 0 {
		panic("golean subject delta D-11: Intn requires n > 0 (the upstream draw panics on a non-positive max)")
	}
	r.mu.Lock()
	draws := make(map[int]struct{}, n)
	for i := 0; i < n; i++ {
		draws[i] = struct{}{}
	}
	v := 0
	for k := range draws {
		v = k
		break
	}
	r.mu.Unlock()
	return v
}"""

# ---- recorded subject patch D-12 (the Q2 logger ruling, W4.2) ------------
#
# W4.2 (docs/raft-w42-log.md item 1; the ruling: docs/raft-w3-log.md §5 Q2,
# harness design §5): upstream logger.go is vendored VERBATIM — the Logger
# interface, SetLogger/getLogger, DefaultLogger and `header` are all upstream
# text, so raft's own assertions (`assertConfStatesEquivalent` via
# Logger.Panic) keep their teeth through whatever Logger the HARNESS installs
# (the harness supplies BOTH seams: raft.SetLogger(...) for the six
# getLogger() sites AND Config.Logger for every r.logger.* call).
#
# The one delta the frontend still forces is the two package-level
# initializers: `log.New(os.Stderr, ...)` / `log.New(io.Discard, ...)` are
# package-selector calls in PACKAGE-LEVEL var initializers, and a var has no
# per-declaration quarantine (G-3 / handoff H-11) — an unlowerable
# initializer refuses the WHOLE export. Until H-11 lands, the initializers
# become bare `&DefaultLogger{}` composite literals and the orphaned `io`
# import is dropped (`fmt`, `log`, `os` stay: DefaultLogger's method bodies
# still name them, and those methods land as per-declaration fail-closed
# stubs, which is the honest shape).
#
# OBSERVABLE WEIGHT, stated: under `go run`, a Logger call BEFORE the
# harness installs its logger would nil-deref inside DefaultLogger (the
# embedded *log.Logger is nil) instead of printing to stderr — loud, never
# silent, and unreachable under the twin, whose first act is SetLogger +
# Config.Logger (the dead-DYNAMICALLY argument, docs/raft-w42-log.md).
# Under the machine the same call is a fail-closed quarantined stub.
LOGGER_VARS_UPSTREAM = """var (
	defaultLogger = &DefaultLogger{Logger: log.New(os.Stderr, "raft", log.LstdFlags)}
	discardLogger = &DefaultLogger{Logger: log.New(io.Discard, "", 0)}
	raftLoggerMu  sync.Mutex
	raftLogger    = Logger(defaultLogger)
)"""

LOGGER_VARS_PATCHED = """// GOLEAN SUBJECT DELTA D-12 (the Q2 logger ruling — docs/raft-w42-log.md
// item 1): the two initializers lose their `log.New(...)` calls (a
// package-level var has no per-declaration quarantine — G-3/H-11 — so an
// unlowerable initializer refuses the whole export). The harness installs
// its own Logger through BOTH seams before any node exists; a pre-install
// Logger call under `go run` nil-derefs loudly instead of printing.
var (
	defaultLogger = &DefaultLogger{}
	discardLogger = &DefaultLogger{}
	raftLoggerMu  sync.Mutex
	raftLogger    = Logger(defaultLogger)
)"""

# file (by OUT path) -> ordered (exact-once old, new) pairs + imports to drop.
SUBJECT_PATCHES = {
    "raft/raft.go": {
        "swaps": [(INTN_UPSTREAM, INTN_PATCHED)],
        "drop_imports": ["crypto/rand", "math/big"],
    },
    "raft/logger.go": {
        "swaps": [(LOGGER_VARS_UPSTREAM, LOGGER_VARS_PATCHED)],
        "drop_imports": ["io"],
    },
}


def apply_subject_patches(outp, text):
    """Apply the recorded patches for one output file (fail closed)."""
    spec = SUBJECT_PATCHES.get(outp)
    if spec is None:
        return text, 0
    for old, new in spec["swaps"]:
        if text.count(old) != 1:
            refuse("subject patch for %s: expected text occurs %d times "
                   "(must be exactly once) — upstream moved under the patch; "
                   "re-read it:\n%s" % (outp, text.count(old), old[:120]))
        text = text.replace(old, new)
    # The residual-reference check ranges over CODE, not comments
    # (upstream's own doc comment above lockedRand says "rand.Rand").
    code = "\n".join(re.sub(r"//.*$", "", ln) for ln in text.split("\n"))
    for pkg in spec["drop_imports"]:
        text, n = re.subn(r'^\t(?:\w+ )?"%s"\n' % re.escape(pkg), "", text,
                          count=1, flags=re.M)
        if not n:
            refuse("subject patch for %s: import %r to drop is not present" % (outp, pkg))
        if re.search(r"\b%s\." % re.escape(pkg.split("/")[-1]), code):
            refuse("subject patch for %s: the code still references %s after "
                   "dropping its import" % (outp, pkg))
    return text, len(spec["swaps"]) + len(spec["drop_imports"])


# Packages that exist in the subject tree, hence whose import paths get
# rewritten from the module path to the short dot-free form.
SUBJECT_PACKAGES = ["confchange", "quorum", "raftpb", "tracker"]

MODULE_PATH = "go.etcd.io/raft/v3"


def refuse(msg):
    sys.stderr.write("derive.py: REFUSED: %s\n" % msg)
    sys.exit(2)


# ------------------------------------------------------ declaration split ----

DECL_START = re.compile(r"^(package|func|type|var|const|import|//|/\*)")


def split_decls(src):
    """Split gofmt'd Go source into top-level chunks.

    A chunk begins at any column-0 line matching DECL_START and runs to the
    line before the next such line.  Sound for gofmt'd code because everything
    inside a declaration is indented (the only column-0 lines are the closing
    `}` / `)`).  Guarded by two checks: no MULTI-LINE raw string literal may
    exist (single-line ones are fine, and struct tags are exactly that) —
    that is the only place a column-0 `func` could hide — and the chunks must
    reassemble the file byte-for-byte.
    """
    lines = src.split("\n")
    for ln in lines:
        if ln.count("`") % 2 != 0:
            refuse("raft.pb.go contains a multi-line raw string literal; the "
                   "column-0 declaration splitter is no longer sound — "
                   "re-read the file: %r" % ln[:60])
    starts = [i for i, ln in enumerate(lines) if DECL_START.match(ln)]
    if not starts:
        refuse("no top-level declarations found")
    chunks = []
    head = "\n".join(lines[: starts[0]])
    for k, i in enumerate(starts):
        j = starts[k + 1] if k + 1 < len(starts) else len(lines)
        chunks.append("\n".join(lines[i:j]))
    rebuilt = head
    if head:
        rebuilt += "\n"
    rebuilt += "\n".join(chunks)
    if rebuilt != src:
        refuse("declaration split did not reassemble the source byte-for-byte")
    return head, chunks


def strip_comment(chunk):
    """Return (leading comment lines, declaration text)."""
    lines = chunk.split("\n")
    k = 0
    while k < len(lines) and (lines[k].startswith("//") or lines[k].strip() == ""):
        k += 1
    return "\n".join(lines[:k]), "\n".join(lines[k:])


# ------------------------------------------------------ plainpb transform ----

PROTOIMPL_FIELD_TYPES = {
    "protoimpl.MessageState",
    "protoimpl.UnknownFields",
    "protoimpl.SizeCache",
}

DROPPED_IMPORTS = {"reflect", "sync", "unsafe",
                   "protoreflect", "protoimpl"}

# Declaration names belonging to the file-descriptor machinery.  Every one is
# DROPPED: the shim declares wire types, it does not register them with a
# protobuf runtime that is not present.  Nothing silently returns a zero
# descriptor — the ACCESSORS (Descriptor / EnumDescriptor / String /
# UnmarshalJSON) become panicking stubs, so any path that would have consumed
# the registration hits an explicit refusal instead.
DESCRIPTOR_DECLS = re.compile(
    r"^(var|const|func)\s+\(?\s*(File_raft_proto|file_raft_proto_\w+)"
)

STUB_BODY = (
    "\tpanic(\"plainpb: %s is a fail-closed stub "
    "(protobuf runtime engineered out; docs/raft-w2-log.md)\")"
)


class Msg:
    def __init__(self, name):
        self.name = name
        self.fields = []  # (name, gotype, tag)


def parse_struct(decl):
    m = re.match(r"^type (\w+) struct \{$", decl.split("\n")[0])
    if not m:
        refuse("unrecognised struct declaration head: %r" % decl.split("\n")[0])
    msg = Msg(m.group(1))
    kept = ["type %s struct {" % msg.name]
    for ln in decl.split("\n")[1:]:
        if ln == "}":
            break
        if ln.strip() == "" or ln.strip().startswith("//"):
            kept.append(ln)
            continue
        fm = re.match(r"^\t(\w+)\s+(\S+)(\s+`[^`]*`)?$", ln)
        if not fm:
            refuse("unrecognised struct field in %s: %r" % (msg.name, ln))
        fname, ftype, ftag = fm.group(1), fm.group(2), (fm.group(3) or "")
        if ftype in PROTOIMPL_FIELD_TYPES:
            continue  # T3: strip the protobuf runtime's private fields
        if "protoimpl" in ftype or "protoreflect" in ftype:
            refuse("unknown protobuf-runtime field type in %s: %s %s"
                   % (msg.name, fname, ftype))
        msg.fields.append((fname, ftype, ftag.strip()))
        kept.append(ln)
    kept.append("}")
    # Re-gofmt the kept field block (dropping the state field changes the
    # alignment column); gofmt runs over the whole file at the end.
    return msg, "\n".join(kept)


GETTER_PTR = re.compile(
    r"^func \(x \*(\w+)\) Get(\w+)\(\) ([\w\.\*\[\]]+) \{\n"
    r"\tif x != nil && x\.(\w+) != nil \{\n"
    r"\t\treturn \*x\.(\w+)\n"
    r"\t\}\n"
    r"\treturn (.+)\n"
    r"\}$"
)
GETTER_VAL = re.compile(
    r"^func \(x \*(\w+)\) Get(\w+)\(\) ([\w\.\*\[\]]+) \{\n"
    r"\tif x != nil \{\n"
    r"\t\treturn x\.(\w+)\n"
    r"\t\}\n"
    r"\treturn (.+)\n"
    r"\}$"
)


def check_getter(decl, msgs):
    """Verify a generated getter has one of the two canonical shapes and
    names a real field of its receiver.  Getters are KEPT verbatim — they are
    plain Go and raft's logic calls them on every normal path — so the check
    is what makes 'kept verbatim' a claim rather than an assumption."""
    m = GETTER_PTR.match(decl)
    if m:
        recv, getter, _rt, f1, f2, _zero = m.groups()
        if f1 != f2 or getter != f1:
            refuse("getter/field mismatch: %s.Get%s reads %s/%s"
                   % (recv, getter, f1, f2))
        kind = "ptr"
    else:
        m = GETTER_VAL.match(decl)
        if not m:
            refuse("getter is not in a recognised canonical shape:\n%s" % decl)
        recv, getter, _rt, f1, zero = m.groups()
        if getter != f1:
            refuse("getter/field mismatch: %s.Get%s reads %s" % (recv, getter, f1))
        if zero != "nil":
            refuse("value-shaped getter %s.Get%s returns non-nil zero %r"
                   % (recv, getter, zero))
        kind = "val"
    msg = msgs.get(recv)
    if msg is None:
        refuse("getter on unknown message type %s" % recv)
    fld = [f for f in msg.fields if f[0] == m.group(2)]
    if not fld:
        refuse("getter %s.Get%s names no field of the stripped struct"
               % (recv, m.group(2)))
    ftype = fld[0][1]
    if kind == "ptr" and not ftype.startswith("*"):
        refuse("pointer-shaped getter over non-pointer field %s.%s %s"
               % (recv, fld[0][0], ftype))
    if kind == "val" and ftype.startswith("*") and ftype[1:] not in msgs:
        refuse("value-shaped getter over optional scalar field %s.%s %s"
               % (recv, fld[0][0], ftype))
    return decl


ENUM_ENUM = re.compile(
    r"^func \(x (\w+)\) Enum\(\) \*\1 \{\n"
    r"\tp := new\(\1\)\n"
    r"\t\*p = x\n"
    r"\treturn p\n"
    r"\}$"
)


def plainpb(src):
    head, chunks = split_decls(src)
    msgs = {}
    enums = set()
    out = []
    dropped = []
    stubbed = []

    # First pass: collect the type declarations (structs and enums), because
    # the getter check and the clone/equal generation need the field lists.
    for chunk in chunks:
        _, decl = strip_comment(chunk)
        if re.match(r"^type (\w+) struct \{$", decl.split("\n")[0] if decl else ""):
            msg, _ = parse_struct(decl)
            msgs[msg.name] = msg
        m = re.match(r"^type (\w+) int32$", decl)
        if m:
            enums.add(m.group(1))

    for chunk in chunks:
        comment, decl = strip_comment(chunk)
        if not decl.strip():
            continue
        first = decl.split("\n")[0]
        emit = None

        if first.startswith("package "):
            # The generated-code banner and the package clause are replaced by
            # this derivation's own header (PLAINPB_HEADER), which says what
            # the file now IS.
            if first != "package raftpb":
                refuse("unexpected package clause: %r" % first)
            continue
        if first.startswith("import ("):
            # The whole import block goes: every one of its entries is a
            # protobuf-runtime package (asserted in DROPPED_IMPORTS), and the
            # stripped file needs no imports at all.
            for ln in decl.split("\n")[1:]:
                if ln == ")" or ln.strip() == "":
                    continue
                name = re.match(r'^\t(\w+) "([^"]+)"$', ln)
                if not name or name.group(1) not in DROPPED_IMPORTS:
                    refuse("unexpected import in raft.pb.go: %r "
                           "— the strip assumes every import is protobuf "
                           "runtime" % ln)
            dropped.append("import block (%s)" % ", ".join(sorted(DROPPED_IMPORTS)))
            continue
        if re.match(r"^const \($", first) and "EnforceVersion" in decl:
            dropped.append("protoimpl version-enforcement const block")
            continue
        if DESCRIPTOR_DECLS.match(first) or \
                first == "func init() { file_raft_proto_init() }" or \
                (first in ("var (", "const (") and "file_raft_proto" in decl):
            dropped.append(first if "file_raft_proto" not in first
                           else first.split("=")[0].strip())
            continue

        # --- enums ---------------------------------------------------------
        m = re.match(r"^type (\w+) int32$", decl)
        if m:
            emit = decl
        elif re.match(r"^const \($", first) and re.search(r"^\t\w+_\w+\s+\w+ = \d+", decl, re.M):
            emit = decl
        elif re.match(r"^var \($", first) and re.search(r"_(name|value) = map", decl):
            emit = decl
        elif ENUM_ENUM.match(decl):
            emit = decl  # T12: plain Go, kept verbatim
        elif re.match(r"^func \(x (\w+)\) String\(\) string \{$", first) and \
                re.match(r"^func \(x (\w+)\)", first).group(1) in enums:
            name = re.match(r"^func \(x (\w+)\)", first).group(1)
            emit = "func (x %s) String() string {\n%s\n}" % (
                name, STUB_BODY % ("%s.String" % name))
            stubbed.append("%s.String" % name)
        elif re.match(r"^func \((\w+)\) Descriptor\(\) protoreflect\.EnumDescriptor", first) or \
                re.match(r"^func \((\w+)\) Type\(\) protoreflect\.EnumType", first) or \
                re.match(r"^func \(x (\w+)\) Number\(\) protoreflect\.EnumNumber", first):
            dropped.append(first)
            continue
        elif re.match(r"^func \(x \*(\w+)\) UnmarshalJSON\(b \[\]byte\) error \{$", first):
            name = re.match(r"^func \(x \*(\w+)\)", first).group(1)
            emit = "func (x *%s) UnmarshalJSON(b []byte) error {\n%s\n}" % (
                name, STUB_BODY % ("%s.UnmarshalJSON" % name))
            stubbed.append("%s.UnmarshalJSON" % name)
        elif re.match(r"^func \((\w+)\) EnumDescriptor\(\) \(\[\]byte, \[\]int\)", first):
            name = re.match(r"^func \((\w+)\)", first).group(1)
            emit = "func (%s) EnumDescriptor() ([]byte, []int) {\n%s\n}" % (
                name, STUB_BODY % ("%s.EnumDescriptor" % name))
            stubbed.append("%s.EnumDescriptor" % name)

        # --- messages ------------------------------------------------------
        elif re.match(r"^type (\w+) struct \{$", first):
            _, emit = parse_struct(decl)
        elif re.match(r"^func \(x \*(\w+)\) Reset\(\) \{$", first):
            name = re.match(r"^func \(x \*(\w+)\)", first).group(1)
            if "protoimpl" not in decl:
                refuse("Reset for %s no longer touches protoimpl — re-read it" % name)
            emit = "func (x *%s) Reset() {\n\t*x = %s{}\n}" % (name, name)
        elif re.match(r"^func \(x \*(\w+)\) String\(\) string \{$", first):
            name = re.match(r"^func \(x \*(\w+)\)", first).group(1)
            emit = "func (x *%s) String() string {\n%s\n}" % (
                name, STUB_BODY % ("%s.String" % name))
            stubbed.append("*%s.String" % name)
        elif re.match(r"^func \(\*(\w+)\) ProtoMessage\(\) \{\}$", first):
            emit = decl  # marker method, plain Go
        elif re.match(r"^func \(x \*(\w+)\) ProtoReflect\(\) protoreflect\.Message \{$", first):
            dropped.append(first)
            continue
        elif re.match(r"^func \(\*(\w+)\) Descriptor\(\) \(\[\]byte, \[\]int\) \{$", first):
            name = re.match(r"^func \(\*(\w+)\)", first).group(1)
            emit = "func (*%s) Descriptor() ([]byte, []int) {\n%s\n}" % (
                name, STUB_BODY % ("%s.Descriptor" % name))
            stubbed.append("*%s.Descriptor" % name)
        elif re.match(r"^func \(x \*(\w+)\) Get(\w+)\(\)", first):
            emit = check_getter(decl, msgs)

        if emit is None:
            refuse("no derivation rule for top-level declaration:\n%s"
                   % decl.split("\n")[0])
        if comment.strip():
            emit = comment.rstrip("\n") + "\n" + emit
        out.append(emit)

    body = "\n\n".join(out)
    if "protoimpl" in body or "protoreflect" in body or "unsafe." in body:
        refuse("protobuf runtime survived the strip — check the rule table")

    header = PLAINPB_HEADER % (PINNED_RAFT_REV[:7], len(msgs), len(enums),
                               len(stubbed))
    return header + "\npackage raftpb\n\n" + body + "\n", msgs, enums, stubbed, dropped


PLAINPB_HEADER = """// Code DERIVED from etcd-io/raft raftpb/raft.pb.go by
// tools/raftsubject/derive.py. DO NOT EDIT — edit the derivation.
//
// This is the `plainpb` shim ruled on 2026-08-19
// (docs/2026-08-15_raft-push-p0-scoping.md §8.6): raft's WIRE TYPES,
// DECLARED rather than generated, so the current library's LOGIC can be
// verified without the protobuf runtime (reflect / unsafe / sync) entering
// the trust surface.
//
// Upstream: deps/raft @ %s, protoc-gen-go v1.36.11, syntax proto2.
// Kept: %d message structs (field numbers preserved in the struct tags),
// %d enums with their constants and name/value maps, every generated getter
// (verbatim, shape-checked by the derivation), Enum(), ProtoMessage(),
// Reset() reduced to its plain-Go half.
// Fail-closed stubs: %d (String, Descriptor, EnumDescriptor, UnmarshalJSON).
// Dropped: the file-descriptor machinery and ProtoReflect (see the log's
// subject-delta ledger for the itemised list and the reasoning).
//
// WIRE CODEC (W4.1, H-1 discharged — docs/raft-w41-log.md item 1): the
// per-type Marshal/Unmarshal/Size live in the generated plain_codec.go
// (AppendMessage / SizeMessage / UnmarshalMessage), derived from the field
// numbers and wire types pinned in the struct tags below. The byte-format
// contract is protobuf wire compatibility for exactly these nine messages;
// the differential obligation is difftest.py section 7 (vs the real
// protobuf runtime) plus the in-sandbox codeccheck.py battery."""


# ------------------------------------------- generated clone / equality ----

CLONE_HEADER = """// Code GENERATED by tools/raftsubject/derive.py from the message field
// lists parsed out of raft.pb.go. DO NOT EDIT — edit the derivation.
//
// Plain-Go replacements for the two protobuf-runtime functions raft calls on
// its NORMAL paths (so marshal-avoidance does not remove them; scoping §7
// layer C names both as residue):
//
//   proto.Clone  -> x.CloneMessage()   deep copy
//   proto.Equal  -> x.EqualMessage(y)  structural equality
//
// proto2 presence semantics, which is what these must reproduce: an optional
// scalar/bytes field is SET iff its pointer (or, for bytes, its slice) is
// non-nil, and unset != set-to-zero. Repeated fields have no presence, so
// nil and empty are equal. These carry a DIFFERENTIAL OBLIGATION against
// upstream proto.Clone/proto.Equal — see docs/raft-w2-log.md.

package raftpb
"""


def gen_clone(msgs, enums):
    order = list(msgs.keys())
    out = [CLONE_HEADER]
    for name in order:
        msg = msgs[name]
        c = ["// CloneMessage returns a deep copy of x. A nil receiver clones to nil,",
             "// matching proto.Clone's treatment of a nil message.",
             "func (x *%s) CloneMessage() *%s {" % (name, name),
             "\tif x == nil {",
             "\t\treturn nil",
             "\t}",
             "\tout := &%s{}" % name]
        e = ["// EqualMessage reports whether x and y carry the same fields with the",
             "// same presence. Two nil messages are equal; nil and non-nil are not.",
             "func (x *%s) EqualMessage(y *%s) bool {" % (name, name),
             "\tif x == nil || y == nil {",
             "\t\treturn x == nil && y == nil",
             "\t}"]
        for fname, ftype, _tag in msg.fields:
            base = ftype.lstrip("*[]")
            if ftype.startswith("*") and (base in enums or base in ("uint64", "bool")):
                # optional scalar / enum: presence-carrying pointer
                c += ["\tif x.%s != nil {" % fname,
                      "\t\tv := *x.%s" % fname,
                      "\t\tout.%s = &v" % fname,
                      "\t}"]
                e += ["\tif (x.%s == nil) != (y.%s == nil) {" % (fname, fname),
                      "\t\treturn false",
                      "\t}",
                      "\tif x.%s != nil && *x.%s != *y.%s {" % (fname, fname, fname),
                      "\t\treturn false",
                      "\t}"]
            elif ftype.startswith("*") and base in msgs:
                c += ["\tout.%s = x.%s.CloneMessage()" % (fname, fname)]
                e += ["\tif (x.%s == nil) != (y.%s == nil) {" % (fname, fname),
                      "\t\treturn false",
                      "\t}",
                      "\tif x.%s != nil && !x.%s.EqualMessage(y.%s) {" % (fname, fname, fname),
                      "\t\treturn false",
                      "\t}"]
            elif ftype == "[]byte":
                # optional bytes: nil is unset, empty-non-nil is set-to-empty
                c += ["\tif x.%s != nil {" % fname,
                      "\t\tout.%s = make([]byte, len(x.%s))" % (fname, fname),
                      "\t\t_ = copy(out.%s, x.%s)" % (fname, fname),
                      "\t}"]
                e += ["\tif (x.%s == nil) != (y.%s == nil) {" % (fname, fname),
                      "\t\treturn false",
                      "\t}",
                      "\tif len(x.%s) != len(y.%s) {" % (fname, fname),
                      "\t\treturn false",
                      "\t}",
                      "\tfor i := range x.%s {" % fname,
                      "\t\tif x.%s[i] != y.%s[i] {" % (fname, fname),
                      "\t\t\treturn false",
                      "\t\t}",
                      "\t}"]
            elif ftype.startswith("[]*") and base in msgs:
                # len>0, not != nil: a repeated field has NO presence, and
                # proto.Clone (which ranges over POPULATED fields) leaves an
                # empty one unset — so an empty-non-nil slice clones to nil.
                # Probed and pinned by tools/raftsubject/difftest.py section 6.
                c += ["\tif len(x.%s) > 0 {" % fname,
                      "\t\tout.%s = make([]*%s, len(x.%s))" % (fname, base, fname),
                      "\t\tfor i := range x.%s {" % fname,
                      "\t\t\tout.%s[i] = x.%s[i].CloneMessage()" % (fname, fname),
                      "\t\t}",
                      "\t}"]
                e += ["\tif len(x.%s) != len(y.%s) {" % (fname, fname),
                      "\t\treturn false",
                      "\t}",
                      "\tfor i := range x.%s {" % fname,
                      "\t\tif !x.%s[i].EqualMessage(y.%s[i]) {" % (fname, fname),
                      "\t\t\treturn false",
                      "\t\t}",
                      "\t}"]
            elif ftype.startswith("[]") and base in ("uint64",):
                # len>0: see the repeated-message arm above. (Contrast the
                # []byte arm, which uses != nil — proto2 optional bytes DO
                # carry presence, so set-to-empty is distinct from unset.)
                c += ["\tif len(x.%s) > 0 {" % fname,
                      "\t\tout.%s = make([]%s, len(x.%s))" % (fname, base, fname),
                      "\t\t_ = copy(out.%s, x.%s)" % (fname, fname),
                      "\t}"]
                e += ["\tif len(x.%s) != len(y.%s) {" % (fname, fname),
                      "\t\treturn false",
                      "\t}",
                      "\tfor i := range x.%s {" % fname,
                      "\t\tif x.%s[i] != y.%s[i] {" % (fname, fname),
                      "\t\t\treturn false",
                      "\t\t}",
                      "\t}"]
            else:
                refuse("no clone/equal rule for field %s.%s of type %s"
                       % (name, fname, ftype))
        c += ["\treturn out", "}"]
        e += ["\treturn true", "}"]
        out.append("\n".join(c))
        out.append("\n".join(e))
    return "\n\n".join(out) + "\n"


# ----------------------------------------------- generated wire codec ------
#
# W4.1 (H-1): a plainpb codec — per-type SizeMessage / AppendMessage /
# UnmarshalMessage — generated from the SAME parsed field lists as the
# clone/equality code, cross-checked against the struct tags protoc-gen-go
# pinned (wire type + field number + opt/rep mode).  The fidelity bar is BYTE
# COMPATIBILITY with the protobuf wire format for exactly these nine message
# types; the arguments and their validation live in docs/raft-w41-log.md
# item 1 (JC-14/JC-15).  Anything the rules below do not recognise REFUSES.

CODEC_HEADER = """// Code GENERATED by tools/raftsubject/derive.py from the message field
// lists parsed out of raft.pb.go, cross-checked against the struct tags
// (wire type, field number, opt/rep mode). DO NOT EDIT — edit the
// derivation.
//
// The plainpb WIRE CODEC (W4.1, H-1 — docs/raft-w41-log.md item 1):
//
//   (x *T) SizeMessage() int           == len(x.AppendMessage(nil))
//   (x *T) AppendMessage(b) []byte     appends the protobuf wire encoding
//   (x *T) UnmarshalMessage(b) error   parses and MERGES into x
//
// Encoding contract (JC-15): fields in FIELD-NUMBER order; proto2
// presence (a set-but-zero optional scalar and a present-but-empty bytes
// field are both emitted); repeated varints UNPACKED (the pinned proto2
// default).  Decoding contract (JC-14): merge semantics (proto.Unmarshal
// = Reset + merge, done in the proto package dispatch); scalars last-one-
// wins with a fresh cell; embedded messages merge; repeated fields
// append; PACKED repeated varints are accepted although never emitted;
// unknown fields and wrong-wire-type known fields are SKIPPED (delta vs
// the runtime's unknown-field preservation, recorded in the log); wire
// types 3/4 (groups — absent from all nine schemas) and malformed input
// return an error.  Varint bounds are protobuf-go's ConsumeVarint's
// (<= 10 bytes, 10th byte <= 1).
//
// The differential obligation: difftest.py section 7 (byte equality vs
// the real protobuf runtime — OWED where the module cache is denied, see
// the log) and codeccheck.py (round-trip, Size = len∘Marshal, and
// hand-verified golden byte sequences, under BOTH go run and the
// machine).

package raftpb

import "errors"

// errPlainpbMalformed is the codec's single decode error. raft observes
// only the nil-ness of an Unmarshal error (never its text or identity
// against other sentinels), so one sentinel suffices; the message names
// the codec for human readers of a differential transcript.
var errPlainpbMalformed = errors.New("plainpb: malformed wire input")

func plainpbSizeVarint(v uint64) int {
	n := 1
	for v >= 0x80 {
		v >>= 7
		n++
	}
	return n
}

func plainpbAppendVarint(b []byte, v uint64) []byte {
	for v >= 0x80 {
		b = append(b, byte(v)|0x80)
		v >>= 7
	}
	return append(b, byte(v))
}

// plainpbConsumeVarint parses a base-128 varint at b[i:], returning the
// value and the index just past it. ok=false on truncation or 64-bit
// overflow (protobuf-go's bounds: at most 10 bytes, the 10th <= 1;
// non-canonical over-long encodings of small values are accepted, as the
// wire format requires).
func plainpbConsumeVarint(b []byte, i int) (uint64, int, bool) {
	var v uint64
	for k := 0; k < 10; k++ {
		if i+k >= len(b) {
			return 0, 0, false
		}
		c := b[i+k]
		if k == 9 && c > 1 {
			return 0, 0, false
		}
		v |= uint64(c&0x7f) << (7 * k)
		if c < 0x80 {
			return v, i + k + 1, true
		}
	}
	return 0, 0, false
}

// plainpbSkipField skips one unknown (or wrong-wire-type) field body.
// Wire types 3/4 (groups) fail: no group exists in any plainpb schema,
// so bytes claiming one are not a valid encoding of these messages.
func plainpbSkipField(b []byte, i int, wire uint64) (int, bool) {
	switch wire {
	case 0:
		_, j, ok := plainpbConsumeVarint(b, i)
		if !ok {
			return 0, false
		}
		return j, true
	case 1:
		if len(b)-i < 8 {
			return 0, false
		}
		return i + 8, true
	case 2:
		n, j, ok := plainpbConsumeVarint(b, i)
		if !ok || uint64(len(b)-j) < n {
			return 0, false
		}
		return j + int(n), true
	case 5:
		if len(b)-i < 4 {
			return 0, false
		}
		return i + 4, true
	}
	return 0, false
}
"""


def parse_field_tag(msg_name, fname, ftag):
    """Parse `protobuf:"varint,2,opt,name=Term"` -> (wiretype, num, mode)."""
    m = re.search(r'protobuf:"([^"]*)"', ftag)
    if not m:
        refuse("field %s.%s has no protobuf struct tag" % (msg_name, fname))
    parts = m.group(1).split(",")
    if len(parts) < 3 or parts[0] not in ("varint", "bytes") or \
            not parts[1].isdigit() or parts[2] not in ("opt", "rep"):
        refuse("unrecognised protobuf tag on %s.%s: %r — extend the codec "
               "rules after READING the new wire shape" % (msg_name, fname, m.group(1)))
    if "packed" in parts:
        refuse("field %s.%s is PACKED — the codec emits unpacked repeated "
               "varints per the proto2 default; a packed field is a schema "
               "change to read, not to skip" % (msg_name, fname))
    return parts[0], int(parts[1]), parts[2]


def classify_field(msgs, enums, msg_name, fname, ftype, ftag):
    """-> (kind, num) with kind in {scalar-u64, scalar-bool, scalar-enum,
    bytes, msg, rep-u64, rep-msg}; cross-checked against the struct tag."""
    wt, num, mode = parse_field_tag(msg_name, fname, ftag)
    base = ftype.lstrip("*[]")
    if ftype == "*uint64":
        kind = "scalar-u64"
    elif ftype == "*bool":
        kind = "scalar-bool"
    elif ftype.startswith("*") and base in enums:
        kind = "scalar-enum"
    elif ftype == "[]byte":
        kind = "bytes"
    elif ftype.startswith("*") and base in msgs:
        kind = "msg"
    elif ftype == "[]uint64":
        kind = "rep-u64"
    elif ftype.startswith("[]*") and base in msgs:
        kind = "rep-msg"
    else:
        refuse("no codec rule for field %s.%s of type %s" % (msg_name, fname, ftype))
    want = {"scalar-u64": ("varint", "opt"), "scalar-bool": ("varint", "opt"),
            "scalar-enum": ("varint", "opt"), "bytes": ("bytes", "opt"),
            "msg": ("bytes", "opt"), "rep-u64": ("varint", "rep"),
            "rep-msg": ("bytes", "rep")}[kind]
    if (wt, mode) != want:
        refuse("field %s.%s: struct tag says (%s,%s) but the Go type %s "
               "implies (%s,%s) — the schema moved under the codec rules"
               % (msg_name, fname, wt, mode, ftype, want[0], want[1]))
    return kind, num


def gen_codec(msgs, enums):
    out = [CODEC_HEADER]
    for name in msgs:
        msg = msgs[name]
        fields = []
        for fname, ftype, ftag in msg.fields:
            kind, num = classify_field(msgs, enums, name, fname, ftype, ftag)
            fields.append((num, fname, ftype, kind))
        fields.sort()
        nums = [num for num, _f, _t, _k in fields]
        if len(set(nums)) != len(nums):
            refuse("duplicate field numbers in %s: %s" % (name, nums))
        if any(num <= 0 or num >= 16 for num in nums):
            # All nine schemas top out at field 14, so every tag fits one
            # byte and the generator emits tags as single-byte constants.
            # A schema with a higher number is a change to READ.
            refuse("field number outside 1..15 in %s: %s — the single-byte "
                   "tag assumption no longer holds" % (name, nums))

        # ---- SizeMessage --------------------------------------------------
        s = ["// SizeMessage returns len(x.AppendMessage(nil)) without",
             "// allocating. A nil receiver sizes to 0 (proto.Size of a nil",
             "// message).",
             "func (x *%s) SizeMessage() int {" % name,
             "\tif x == nil {",
             "\t\treturn 0",
             "\t}",
             "\tn := 0"]
        for num, fname, ftype, kind in fields:
            base = ftype.lstrip("*[]")
            if kind == "scalar-u64":
                s += ["\tif x.%s != nil {" % fname,
                      "\t\tn += 1 + plainpbSizeVarint(*x.%s)" % fname,
                      "\t}"]
            elif kind == "scalar-bool":
                s += ["\tif x.%s != nil {" % fname,
                      "\t\tn += 2",
                      "\t}"]
            elif kind == "scalar-enum":
                s += ["\tif x.%s != nil {" % fname,
                      "\t\tn += 1 + plainpbSizeVarint(uint64(*x.%s))" % fname,
                      "\t}"]
            elif kind == "bytes":
                s += ["\tif x.%s != nil {" % fname,
                      "\t\tn += 1 + plainpbSizeVarint(uint64(len(x.%s))) + len(x.%s)" % (fname, fname),
                      "\t}"]
            elif kind == "msg":
                s += ["\tif x.%s != nil {" % fname,
                      "\t\ts := x.%s.SizeMessage()" % fname,
                      "\t\tn += 1 + plainpbSizeVarint(uint64(s)) + s",
                      "\t}"]
            elif kind == "rep-u64":
                s += ["\tfor _, v := range x.%s {" % fname,
                      "\t\tn += 1 + plainpbSizeVarint(v)",
                      "\t}"]
            elif kind == "rep-msg":
                s += ["\tfor _, e := range x.%s {" % fname,
                      "\t\ts := e.SizeMessage()",
                      "\t\tn += 1 + plainpbSizeVarint(uint64(s)) + s",
                      "\t}"]
        s += ["\treturn n", "}"]
        out.append("\n".join(s))

        # ---- AppendMessage ------------------------------------------------
        a = ["// AppendMessage appends x's protobuf wire encoding to b, fields",
             "// in field-number order. A nil receiver appends nothing.",
             "func (x *%s) AppendMessage(b []byte) []byte {" % name,
             "\tif x == nil {",
             "\t\treturn b",
             "\t}"]
        for num, fname, ftype, kind in fields:
            wt = {"scalar-u64": 0, "scalar-bool": 0, "scalar-enum": 0,
                  "bytes": 2, "msg": 2, "rep-u64": 0, "rep-msg": 2}[kind]
            tag = "0x%02x" % (num << 3 | wt)
            if kind == "scalar-u64":
                a += ["\tif x.%s != nil {" % fname,
                      "\t\tb = append(b, %s)" % tag,
                      "\t\tb = plainpbAppendVarint(b, *x.%s)" % fname,
                      "\t}"]
            elif kind == "scalar-bool":
                a += ["\tif x.%s != nil {" % fname,
                      "\t\tb = append(b, %s)" % tag,
                      "\t\tif *x.%s {" % fname,
                      "\t\t\tb = append(b, 1)",
                      "\t\t} else {",
                      "\t\t\tb = append(b, 0)",
                      "\t\t}",
                      "\t}"]
            elif kind == "scalar-enum":
                a += ["\tif x.%s != nil {" % fname,
                      "\t\tb = append(b, %s)" % tag,
                      "\t\tb = plainpbAppendVarint(b, uint64(*x.%s))" % fname,
                      "\t}"]
            elif kind == "bytes":
                a += ["\tif x.%s != nil {" % fname,
                      "\t\tb = append(b, %s)" % tag,
                      "\t\tb = plainpbAppendVarint(b, uint64(len(x.%s)))" % fname,
                      "\t\tb = append(b, x.%s...)" % fname,
                      "\t}"]
            elif kind == "msg":
                a += ["\tif x.%s != nil {" % fname,
                      "\t\tb = append(b, %s)" % tag,
                      "\t\tb = plainpbAppendVarint(b, uint64(x.%s.SizeMessage()))" % fname,
                      "\t\tb = x.%s.AppendMessage(b)" % fname,
                      "\t}"]
            elif kind == "rep-u64":
                a += ["\tfor _, v := range x.%s {" % fname,
                      "\t\tb = append(b, %s)" % tag,
                      "\t\tb = plainpbAppendVarint(b, v)",
                      "\t}"]
            elif kind == "rep-msg":
                a += ["\tfor _, e := range x.%s {" % fname,
                      "\t\tb = append(b, %s)" % tag,
                      "\t\tb = plainpbAppendVarint(b, uint64(e.SizeMessage()))",
                      "\t\tb = e.AppendMessage(b)",
                      "\t}"]
        a += ["\treturn b", "}"]
        out.append("\n".join(a))

        # ---- UnmarshalMessage ---------------------------------------------
        u = ["// UnmarshalMessage parses b and MERGES into x (the proto",
             "// package's Unmarshal resets first; embedded-message fields",
             "// recurse through this merge form, which is what makes a",
             "// twice-encoded singular message field merge as the wire",
             "// format specifies).",
             "func (x *%s) UnmarshalMessage(b []byte) error {" % name,
             "\ti := 0",
             "\tfor i < len(b) {",
             "\t\ttag, j, ok := plainpbConsumeVarint(b, i)",
             "\t\tif !ok {",
             "\t\t\treturn errPlainpbMalformed",
             "\t\t}",
             "\t\ti = j",
             "\t\tnum := tag >> 3",
             "\t\twire := tag & 7",
             "\t\tif num == 0 {",
             "\t\t\treturn errPlainpbMalformed",
             "\t\t}",
             "\t\tswitch {"]
        for num, fname, ftype, kind in fields:
            base = ftype.lstrip("*[]")
            if kind in ("scalar-u64", "rep-u64"):
                u += ["\t\tcase num == %d && wire == 0:" % num,
                      "\t\t\tv, j2, ok2 := plainpbConsumeVarint(b, i)",
                      "\t\t\tif !ok2 {",
                      "\t\t\t\treturn errPlainpbMalformed",
                      "\t\t\t}"]
                if kind == "scalar-u64":
                    u += ["\t\t\tx.%s = &v" % fname]
                else:
                    u += ["\t\t\tx.%s = append(x.%s, v)" % (fname, fname)]
                u += ["\t\t\ti = j2"]
                if kind == "rep-u64":
                    # Packed acceptance (JC-14): never emitted, always parsed.
                    u += ["\t\tcase num == %d && wire == 2:" % num,
                          "\t\t\tn, j2, ok2 := plainpbConsumeVarint(b, i)",
                          "\t\t\tif !ok2 || uint64(len(b)-j2) < n {",
                          "\t\t\t\treturn errPlainpbMalformed",
                          "\t\t\t}",
                          "\t\t\tend := j2 + int(n)",
                          "\t\t\tfor j2 < end {",
                          "\t\t\t\tv, k, ok3 := plainpbConsumeVarint(b, j2)",
                          "\t\t\t\tif !ok3 || k > end {",
                          "\t\t\t\t\treturn errPlainpbMalformed",
                          "\t\t\t\t}",
                          "\t\t\t\tx.%s = append(x.%s, v)" % (fname, fname),
                          "\t\t\t\tj2 = k",
                          "\t\t\t}",
                          "\t\t\ti = end"]
            elif kind == "scalar-bool":
                u += ["\t\tcase num == %d && wire == 0:" % num,
                      "\t\t\tv, j2, ok2 := plainpbConsumeVarint(b, i)",
                      "\t\t\tif !ok2 {",
                      "\t\t\t\treturn errPlainpbMalformed",
                      "\t\t\t}",
                      "\t\t\tbv := v != 0",
                      "\t\t\tx.%s = &bv" % fname,
                      "\t\t\ti = j2"]
            elif kind == "scalar-enum":
                u += ["\t\tcase num == %d && wire == 0:" % num,
                      "\t\t\tv, j2, ok2 := plainpbConsumeVarint(b, i)",
                      "\t\t\tif !ok2 {",
                      "\t\t\t\treturn errPlainpbMalformed",
                      "\t\t\t}",
                      "\t\t\tev := %s(int32(uint32(v)))" % base,
                      "\t\t\tx.%s = &ev" % fname,
                      "\t\t\ti = j2"]
            elif kind == "bytes":
                u += ["\t\tcase num == %d && wire == 2:" % num,
                      "\t\t\tn, j2, ok2 := plainpbConsumeVarint(b, i)",
                      "\t\t\tif !ok2 || uint64(len(b)-j2) < n {",
                      "\t\t\t\treturn errPlainpbMalformed",
                      "\t\t\t}",
                      "\t\t\ts := make([]byte, n)",
                      "\t\t\tcopy(s, b[j2:j2+int(n)])",
                      "\t\t\tx.%s = s" % fname,
                      "\t\t\ti = j2 + int(n)"]
            elif kind == "msg":
                u += ["\t\tcase num == %d && wire == 2:" % num,
                      "\t\t\tn, j2, ok2 := plainpbConsumeVarint(b, i)",
                      "\t\t\tif !ok2 || uint64(len(b)-j2) < n {",
                      "\t\t\t\treturn errPlainpbMalformed",
                      "\t\t\t}",
                      "\t\t\tif x.%s == nil {" % fname,
                      "\t\t\t\tx.%s = &%s{}" % (fname, base),
                      "\t\t\t}",
                      "\t\t\tif err := x.%s.UnmarshalMessage(b[j2 : j2+int(n)]); err != nil {" % fname,
                      "\t\t\t\treturn err",
                      "\t\t\t}",
                      "\t\t\ti = j2 + int(n)"]
            elif kind == "rep-msg":
                u += ["\t\tcase num == %d && wire == 2:" % num,
                      "\t\t\tn, j2, ok2 := plainpbConsumeVarint(b, i)",
                      "\t\t\tif !ok2 || uint64(len(b)-j2) < n {",
                      "\t\t\t\treturn errPlainpbMalformed",
                      "\t\t\t}",
                      "\t\t\te := &%s{}" % base,
                      "\t\t\tif err := e.UnmarshalMessage(b[j2 : j2+int(n)]); err != nil {",
                      "\t\t\t\treturn err",
                      "\t\t\t}",
                      "\t\t\tx.%s = append(x.%s, e)" % (fname, fname),
                      "\t\t\ti = j2 + int(n)"]
        u += ["\t\tdefault:",
              "\t\t\tj2, ok2 := plainpbSkipField(b, i, wire)",
              "\t\t\tif !ok2 {",
              "\t\t\t\treturn errPlainpbMalformed",
              "\t\t\t}",
              "\t\t\ti = j2",
              "\t\t}",
              "\t}",
              "\treturn nil",
              "}"]
        out.append("\n".join(u))
    return "\n\n".join(out) + "\n"


# ------------------------------------------------------ verbatim vendor ----

def rewrite_imports(src):
    n = 0
    for pkg in SUBJECT_PACKAGES:
        src, k = re.subn(r'"%s/%s"' % (re.escape(MODULE_PATH), pkg),
                         '"%s"' % pkg, src)
        n += k
    if MODULE_PATH in src:
        refuse("an unrewritten %s import path survived: the subject tree does "
               "not vendor that package yet" % MODULE_PATH)
    # The protobuf runtime import becomes the subject-local `proto` package
    # (emitted below).  Same shape of rewrite as the module-path one and for
    # the same reason: the frontend's case-relative convention has no place
    # for a dotted path, and the tree must name what it actually links.
    src, k = re.subn(r'"%s"' % re.escape(PROTO_PATH), '"proto"', src)
    n += k
    return src, n


# ------------------------------------------------- the proto stand-in ------

PROTO_HEADER = """// Code GENERATED by tools/raftsubject/derive.py. DO NOT EDIT — edit the
// derivation.
//
// The subject-local stand-in for %s, which the
// vendored raft root package calls on four functions.  Since W4.1 (H-1
// discharged — docs/raft-w41-log.md item 1) the four bodies are REAL:
// type-switch dispatch over the nine plainpb message types into the
// generated per-type codec (raftpb/plain_codec.go: AppendMessage /
// SizeMessage / UnmarshalMessage) and deep clone (raftpb/plain_clone.go:
// CloneMessage).  A message type outside the nine cannot exist in the
// subject tree (the derivation refuses unknown proto surface), and the
// dispatch defaults still fail closed with an explicit panic — never a
// silent zero.
//
// Semantics deltas vs the runtime, recorded (JC-14/JC-15 in the log):
// Clone of a TYPED-NIL message returns the typed nil (the runtime returns
// a read-only zero message) — unreachable in the tree, every clone site
// guards or guarantees non-nil; Unmarshal DROPS unknown fields after
// skipping them (the runtime preserves them for re-marshal).

package proto

import (
	"raftpb"
)

// Message is the interface the vendored callers pass.  Every plainpb message
// type satisfies it — the derivation keeps their generated ProtoMessage()
// marker methods verbatim — so the stand-in type-checks exactly where the
// runtime's own proto.Message did.
type Message interface {
	ProtoMessage()
}

// nonNil matches proto.Marshal's empty-message behavior: a valid message
// with nothing to encode marshals to a zero-length NON-NIL slice.
func nonNil(b []byte) []byte {
	if b == nil {
		return []byte{}
	}
	return b
}
"""


def gen_proto(used, msgs):
    """Emit the subject-local proto package for exactly the used functions,
    each a type-switch dispatch over the nine plainpb message types."""
    unknown = sorted(u for u in used if u not in PROTO_FUNCS)
    if unknown:
        refuse("the vendored tree calls proto.%s, which the stand-in does not "
               "declare — read the new call site and extend PROTO_FUNCS "
               "(fail-closed by design)" % ", proto.".join(unknown))
    names = list(msgs.keys())
    out = [PROTO_HEADER % PROTO_PATH]
    for name in sorted(used):
        sig, _res = PROTO_FUNCS[name]
        body = ["%s {" % sig]
        if name == "Clone":
            body += ["\tif m == nil {",
                     "\t\treturn nil",
                     "\t}",
                     "\tswitch x := m.(type) {"]
            for t in names:
                body += ["\tcase *raftpb.%s:" % t,
                         "\t\treturn x.CloneMessage()"]
        elif name == "Marshal":
            body += ["\tswitch x := m.(type) {"]
            for t in names:
                body += ["\tcase *raftpb.%s:" % t,
                         "\t\treturn nonNil(x.AppendMessage(nil)), nil"]
        elif name == "Size":
            body += ["\tswitch x := m.(type) {"]
            for t in names:
                body += ["\tcase *raftpb.%s:" % t,
                         "\t\treturn x.SizeMessage()"]
        elif name == "Unmarshal":
            body += ["\tswitch x := m.(type) {"]
            for t in names:
                body += ["\tcase *raftpb.%s:" % t,
                         "\t\tx.Reset()",
                         "\t\treturn x.UnmarshalMessage(b)"]
        body += ["\t}",
                 '\tpanic("proto: %s on a message type outside the plainpb '
                 'nine (fail closed; extend the derivation after reading '
                 'the new type)")' % name,
                 "}"]
        out.append("\n".join(body))
    return "\n\n".join(out) + "\n"


# ------------------------------------------------ declaration selection ----

def decl_name(decl):
    """The key a `select` rule names a top-level declaration by."""
    head = decl.split("\n")[0]
    m = re.match(r"^func \((?:\w+ )?\*?(\w+)\) (\w+)", head)
    if m:
        return "%s.%s" % (m.group(1), m.group(2))
    for pat, fmt in ((r"^func (\w+)", "%s"), (r"^type (\w+)", "%s"),
                     (r"^(?:var|const) (\w+)", "%s")):
        m = re.match(pat, head)
        if m:
            return fmt % m.group(1)
    m = re.match(r"^(var|const) \($", head)
    if m:
        names = re.findall(r"^\t(\w+)", decl, re.M)
        return "%s(%s)" % (m.group(1), names[0] if names else "?")
    if head.startswith("import"):
        return "$imports"
    if head.startswith("package"):
        return "$package"
    return "?" + head[:40]


def select_decls(src, keep, drop_imports):
    """Keep the named top-level declarations verbatim; drop everything else."""
    _head, chunks = split_decls(src)
    kept, found, dropped = [], set(), []
    for chunk in chunks:
        comment, decl = strip_comment(chunk)
        if not decl.strip():
            continue
        name = decl_name(decl)
        if name in keep:
            found.add(name)
            text = decl.rstrip("\n")
            if comment.strip():
                text = comment.rstrip("\n") + "\n" + text
            kept.append(text)
        else:
            dropped.append(name)
    missing = [k for k in keep if k not in found]
    if missing:
        refuse("select: no such top-level declaration(s): %s — upstream moved "
               "them, so the subset must be re-read" % ", ".join(missing))
    text = "\n\n".join(kept) + "\n"
    for pkg in drop_imports:
        text, n = re.subn(r'^\t(?:\w+ )?"%s"\n' % re.escape(pkg), "", text,
                          count=1, flags=re.M)
        if not n:
            refuse("select: import %r to drop is not in the kept text" % pkg)
        if re.search(r"\b%s\." % re.escape(pkg.split("/")[-1]), text):
            refuse("select: the kept declarations still reference %s after "
                   "dropping its import" % pkg)
    return text, dropped


# ------------------------------------------------------------- driver ------

def digest(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def derive(raft_dir, out_dir, verbose=True):
    rev = subprocess.run(["git", "-C", raft_dir, "rev-parse", "HEAD"],
                         capture_output=True, text=True).stdout.strip()
    if rev != PINNED_RAFT_REV:
        sys.stderr.write(
            "derive.py: NOTE: deps/raft is at %s, the derivation was read "
            "against %s\n" % (rev[:12], PINNED_RAFT_REV[:12]))

    # Digest gate first: refuse before writing anything.
    for up, _out, _mode in VENDOR:
        want = DIGESTS.get(up)
        got = digest(os.path.join(raft_dir, up))
        if not want:
            refuse("no pinned digest for %s (run --print-digests)" % up)
        if want != got:
            refuse("upstream %s changed (%s != pinned %s) — re-read the file "
                   "and its derivation rules before moving the subject tree"
                   % (up, got[:12], want[:12]))

    report = []
    proto_used = set()
    plainpb_msgs = None
    for up, outp, mode in VENDOR:
        src = open(os.path.join(raft_dir, up)).read()
        dst = os.path.join(out_dir, outp)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        if mode == "verbatim":
            text, n = rewrite_imports(src)
            text, npatch = apply_subject_patches(outp, text)
            if npatch:
                report.append("verbatim %-32s (%d import path%s rewritten; "
                              "%d recorded patch action%s — SUBJECT_PATCHES)"
                              % (outp, n, "" if n == 1 else "s",
                                 npatch, "" if npatch == 1 else "s"))
            else:
                report.append("verbatim %-32s (%d import path%s rewritten)"
                              % (outp, n, "" if n == 1 else "s"))
        elif mode == "select":
            text, dropped = select_decls(src, NODE_KEEP, NODE_DROP_IMPORTS)
            text, n = rewrite_imports(text)
            report.append("select   %-32s (%d declarations kept, %d dropped, "
                          "%d import%s rewritten)"
                          % (outp, len(NODE_KEEP) - 2, len(dropped), n,
                             "" if n == 1 else "s"))
        elif mode == "plainpb":
            text, msgs, enums, stubbed, dropped = plainpb(src)
            plainpb_msgs = msgs
            with open(os.path.join(out_dir, "raftpb", "plain_clone.go"), "w") as f:
                f.write(gen_clone(msgs, enums))
            with open(os.path.join(out_dir, "raftpb", "plain_codec.go"), "w") as f:
                f.write(gen_codec(msgs, enums))
            report.append("plainpb  %-32s (%d msgs, %d enums, %d stubs, %d drops)"
                          % (outp, len(msgs), len(enums), len(stubbed), len(dropped)))
            report.append("generate %-32s (CloneMessage/EqualMessage x %d)"
                          % ("raftpb/plain_clone.go", len(msgs)))
            report.append("generate %-32s (Size/Append/UnmarshalMessage x %d)"
                          % ("raftpb/plain_codec.go", len(msgs)))
        elif mode == "overlay":
            ov = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                              "overlay", outp)
            if not os.path.exists(ov):
                refuse("overlay missing: %s" % ov)
            text = open(ov).read()
            report.append("overlay  %-32s (upstream digest pinned)" % outp)
        else:
            refuse("unknown mode %s" % mode)
        # Census the proto surface from CODE, not comments: the confstate
        # overlay's header names `proto.Clone`/`proto.Equal` while describing
        # what it replaced them with, and a stand-in generated from that would
        # declare functions nothing calls.
        code = "\n".join(re.sub(r"//.*$", "", ln) for ln in text.split("\n"))
        proto_used.update(re.findall(r"\bproto\.(\w+)\(", code))
        with open(dst, "w") as f:
            f.write(text)

    if proto_used:
        if plainpb_msgs is None:
            refuse("proto surface used but no plainpb step ran — VENDOR order broken")
        os.makedirs(os.path.join(out_dir, "proto"), exist_ok=True)
        with open(os.path.join(out_dir, "proto", "proto.go"), "w") as f:
            f.write(gen_proto(proto_used, plainpb_msgs))
        report.append("generate %-32s (%d codec dispatch function%s: %s)"
                      % ("proto/proto.go", len(proto_used),
                         "" if len(proto_used) == 1 else "s",
                         ", ".join(sorted(proto_used))))

    gofmt = subprocess.run(["gofmt", "-w", out_dir], capture_output=True, text=True)
    if gofmt.returncode != 0:
        refuse("gofmt failed on the derived tree:\n%s" % gofmt.stderr)

    if verbose:
        for line in report:
            print("derive.py: " + line)
    return report


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--raft", default=os.path.join(REPO, "deps", "raft"))
    ap.add_argument("--out", default=os.path.join(REPO, "raftsubject"))
    ap.add_argument("--check", action="store_true",
                    help="derive to a temp dir and diff against --out")
    ap.add_argument("--print-digests", action="store_true")
    args = ap.parse_args()

    if args.print_digests:
        print("DIGESTS = {")
        for up, _o, _m in VENDOR:
            print('    "%s": "%s",' % (up, digest(os.path.join(args.raft, up))))
        print("}")
        return

    if args.check:
        tmp = tempfile.mkdtemp(prefix="raftsubject-check-")
        try:
            derive(args.raft, tmp, verbose=False)
            drift = []
            for root, _d, files in os.walk(tmp):
                for fn in files:
                    a = os.path.join(root, fn)
                    rel = os.path.relpath(a, tmp)
                    b = os.path.join(args.out, rel)
                    if not os.path.exists(b) or not filecmp.cmp(a, b, shallow=False):
                        drift.append(rel)
            for root, _d, files in os.walk(args.out):
                for fn in files:
                    if not fn.endswith(".go"):
                        continue
                    rel = os.path.relpath(os.path.join(root, fn), args.out)
                    if not os.path.exists(os.path.join(tmp, rel)):
                        drift.append(rel + " (tracked but not derived)")
            if drift:
                sys.stderr.write("derive.py: --check DRIFT:\n")
                for d in sorted(set(drift)):
                    sys.stderr.write("  %s\n" % d)
                sys.exit(1)
            print("derive.py: --check clean (%s matches the derivation)" % args.out)
        finally:
            shutil.rmtree(tmp)
        return

    derive(args.raft, args.out)


if __name__ == "__main__":
    main()
