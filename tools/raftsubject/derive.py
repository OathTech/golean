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
            their struct tags, enums, getters, the unknownFields store) and
            turning every runtime-touching method into a FAIL-CLOSED STUB.
            Additionally EMIT the route A codec (plain_wire.go,
            plain_codec.go, plain_clone.go) from the same parsed field lists,
            each function named after its protobuf-go twin, plus the FuncId
            table tools/raftsubject/codec-funcids.tsv (D8).

  overlay   A hand-written replacement for an upstream file that cannot be
            mechanically stripped (it is hand-written Go that calls into the
            protobuf runtime).  NO file uses it since route A S1 (2026-10-04,
            D7): raftpb/confchange.go is verbatim and raftpb/confstate.go is
            verbatim plus the recorded D-3 patch, as logger.go has been since
            W4.2 (the D-5 no-op overlay retired; verbatim plus D-12).  The
            mode stays, fail-closed, for a future file a patch cannot reach.
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

# PROTO_FUNCS / PROTO_PATH: see the proto stand-in section below (route A).

# Upstream files -> (out path, mode).  Order is the emission order.
VENDOR = [
    ("raftpb/raft.pb.go", "raftpb/raft.pb.go", "plainpb"),
    ("raftpb/alias.go", "raftpb/alias.go", "verbatim"),
    ("raftpb/util.go", "raftpb/util.go", "verbatim"),
    # ROUTE A S1 (D7, Q2 ruled [USER] 2026-10-04): both former overlays
    # retire. confchange.go is upstream VERBATIM (its protobuf import
    # rewritten to the subject-local `proto`, JC-13 / the W2 overlay delta
    # RETIRED); confstate.go is upstream text plus the recorded exact-text
    # patch D-3 on its two fmt.Errorf lines (SUBJECT_PATCHES).
    ("raftpb/confstate.go", "raftpb/confstate.go", "verbatim"),
    ("raftpb/confchange.go", "raftpb/confchange.go", "verbatim"),
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
# carries ONE recorded patch: `(*lockedRand).Intn`'s body becomes ONE call
# into the machine's GENERAL `[0, n)` pick site.
#
# RE-KEYED 2026-09-30 (window unit 5b, lane core/intn-pick-0930; [USER] Mike,
# item 2 of «The raft-proofs team's subject-delta note (2026-09-30) — RULED»,
# relayed: a native `Intn`-style pick site, GENERAL, replacing the map-range
# idiom; design docs/2026-09-30_intn-pick-design.md D6). Before: the first
# key of a range over a fresh n-key map (the map-iteration choice site, with
# a DISTRIBUTION delta under `go run`). Now: `rand.Intn(n)` from `math/rand`
# — the frontend's `rand-intn` primitive, `Stmt.randIntn` / `ChoiceSite.intn`
# (bound n exactly, every value of [0, n) a member; under `go run` a uniform
# draw, as upstream's `crypto/rand.Int` is). The `n <= 0` failure mode is a
# `panic(string)` on both (upstream «crypto/rand: argument to Int is <= 0»,
# here math/rand's «invalid argument to Intn», emitted by the lowering as
# upstream math/rand's own guard) — UNREACHABLE in raft: `Config.validate`
# forces ElectionTick > HeartbeatTick > 0, so n >= 2 at the one call site
# (`resetRandomizedElectionTimeout`). `resetRandomizedElectionTimeout` then
# realizes raft's contract range [electionTimeout, 2*electionTimeout), which
# is what the latitude entry files (W4.5). Upstream itself treats the value
# as injectable (rafttest's set-randomized-election-timeout). Retiring D-11
# to upstream's VERBATIM body needs `crypto/rand.Int` + `crypto/rand.Reader`
# as environment contracts over a `*big.Int` representation (`math/big.NewInt`,
# `(*big.Int).Int64`) — measured by `scripts/lower-diagnose`, POSED in the
# design note (§2 option B), not taken.
#
# The patch is keyed to upstream's EXACT text and fails closed on drift —
# a new rev's Intn must be re-read, not silently re-patched. Subject-delta
# ledger row: D-11 (the W4.1 log; the 2026-09-30 re-key continuation in
# docs/raft-w42-log.md).
INTN_UPSTREAM = """func (r *lockedRand) Intn(n int) int {
	r.mu.Lock()
	v, _ := rand.Int(rand.Reader, big.NewInt(int64(n)))
	r.mu.Unlock()
	return int(v.Int64())
}"""

INTN_PATCHED = """// GOLEAN SUBJECT DELTA D-11 (H-15, the election-jitter CHOICE SITE —
// docs/raft-w41-log.md item 3; RE-KEYED 2026-09-30, window unit 5b:
// docs/2026-09-30_intn-pick-design.md D6). Upstream draws via crypto/rand
// + math/big, which the machine never models (jitter is nondeterminism;
// the envelope, not a stream of modeled bits, is the semantics). The draw
// below is ONE call into the machine's general [0, n) pick site — the
// frontend's rand-intn primitive (GoCore Stmt.randIntn / ChoiceSite.intn:
// bound n exactly, every value of [0, n) a member; under `go run` a uniform
// draw, as upstream's is). The n <= 0 failure mode is a panic(string) on
// both oracles (upstream's text differs; unreachable: Config.validate
// forces n = electionTimeout >= 2). The mutex stays: globalRand is shared
// package state and dropping the lock would smuggle in a concurrency
// delta.
func (r *lockedRand) Intn(n int) int {
	r.mu.Lock()
	v := rand.Intn(n)
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
# initializers: `log.New(os.Stderr, ...)` / `log.New(io.Discard, ...)` do not
# lower, so the initializers become bare `&DefaultLogger{}` composite
# literals and the orphaned `io` import is dropped (`fmt`, `log`, `os` stay:
# DefaultLogger's method bodies still name them, and those methods land as
# per-declaration fail-closed stubs, which is the honest shape).
#
# WHAT WOULD RETIRE THIS DELTA — corrected 2026-08-21 (audit B-F1). An
# earlier version of this comment said "until H-11 lands". That is FALSE:
# H-11, the package-level-var quarantine, SHIPPED in W4.0 (docs/raft-w4-log.md
# item 3). H-11 does not retire D-12, because its per-declaration quarantine
# is GATED on `initializerEffectIsolated` (tools/nativefrontend/emit.go), and
# upstream's initializer is refused there on THREE INDEPENDENT axes, any one
# of which is sufficient:
#   (a) the whole RHS is `&DefaultLogger{...}` — an address-of expression,
#       which the shape allowlist answers false for (a pointer escaping into
#       the cell). This axis holds for the PATCHED bare `&DefaultLogger{}`
#       too, so no amount of argument rewriting gets past it.
#   (b) `log.New` is not in `pureUnmodeledCallees`, so the call answers
#       false. It must NOT be casually added: that allowlist is minimal by
#       charter after audit F1 (2026-08-20, docs/raft-w4-log.md), where
#       `var _ = fmt.Println("x")` was declared effect-isolated and SKIPPED —
#       the machine printed nothing where `go run` printed. Unmodeled is not
#       effect-free, and `log.New` RETAINS a writer whose later writes land
#       on stderr, an oracle-visible surface.
#   (c) even granting (b), the arguments fail `isolatedType`: `os.Stderr` is
#       a `*os.File` (pointer) and `io.Discard` an `io.Writer` (interface),
#       while the predicate admits only basics and arrays/structs of basics.
# So D-12 retires only when the initializer LOWERS — a frontend model for
# `log.New` plus the `io.Writer`/`os.Stderr` surface — or when an
# effect/isolation story for WRITER-TYPED globals is built that is sound in
# audit-F1's sense. That is handoff H-20 (docs/raft-w42-log.md). The honest
# alternative is on the table: D-12 is three code lines, exact-text-keyed,
# refusing on drift, on a path the twin cannot reach — leaving it permanent
# is cheap.
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
// item 1): the two initializers lose their `log.New(...)` calls, which do
// not lower. The harness installs its own Logger through BOTH seams before
// any node exists; a pre-install Logger call under `go run` nil-derefs
// loudly instead of printing.
//
// NOT retired by H-11 (which shipped in W4.0). H-11's per-declaration
// quarantine is gated on `initializerEffectIsolated`, which refuses this
// initializer on three independent axes: the `&`-composite shape, `log.New`
// being outside `pureUnmodeledCallees` (kept minimal by audit F1 — an
// unmodeled call is NOT effect-free), and `os.Stderr`/`io.Discard` failing
// `isolatedType`. Retiring D-12 needs a writer-typed-global effect story:
// handoff H-20. See tools/raftsubject/derive.py for the full argument.
var (
	defaultLogger = &DefaultLogger{}
	discardLogger = &DefaultLogger{}
	raftLoggerMu  sync.Mutex
	raftLogger    = Logger(defaultLogger)
)"""

# ---- recorded subject patch D-3 (route A S1, D7 — the confstate overlay
# RETIRED) ------------------------------------------------------------------
#
# ROUTE A slice S1 (docs/2026-10-04_route-a-protobuf-design.md D7; Q2 ruled
# [USER] Mike 2026-10-04 «Approved», relayed: retire the overlay NOW):
# upstream raftpb/confstate.go is vendored as TEXT — its proto.Clone /
# proto.Equal calls go to the subject-local proto package like every other
# call site — and the ONE residue is D-3's: the two `fmt.Errorf` lines,
# because `fmt` does not lower. Each becomes `errors.New` over the
# format string's fixed text (fmt.Errorf without %w IS errors.New(s) —
# go1.26.5 src/fmt/errors.go — so the error's dynamic type is upstream's;
# its TEXT loses the `(left=…, right=…)` booleans and the four `%+#v`
# dumps). The VERDICT (nil vs non-nil) is unchanged. D-3 is a PERMANENT
# stated inexactness ([USER] 2026-10-04, Q4): upstream's `%+#v` prints the
# runtime's `state` field (a *impl.MessageInfo pointer), which no route can
# reproduce. Keyed to upstream's EXACT text; fails closed on drift.
CONFSTATE_NIL_UPSTREAM = (
    '\t\treturn fmt.Errorf("cannot compare ConfState: nil input (left=%v, right=%v)", cs == nil, cs2 == nil)\n')
CONFSTATE_NIL_PATCHED = (
    '\t\t// GOLEAN SUBJECT DELTA D-3 (route A D7): fmt.Errorf -> errors.New, the\n'
    '\t\t// (left=%v, right=%v) booleans dropped; the verdict is upstream\'s.\n'
    '\t\treturn errors.New("cannot compare ConfState: nil input")\n')
CONFSTATE_NEQ_UPSTREAM = (
    '\t\treturn fmt.Errorf("ConfStates not equivalent after sorting:\\n%+#v\\n%+#v\\nInputs were:\\n%+#v\\n%+#v", cs1v, cs2v, cs, cs2)\n')
CONFSTATE_NEQ_PATCHED = (
    '\t\t// GOLEAN SUBJECT DELTA D-3 (route A D7): fmt.Errorf -> errors.New, the\n'
    '\t\t// four %+#v dumps dropped (permanent: the dump prints the runtime\'s\n'
    '\t\t// state pointer); the verdict is upstream\'s.\n'
    '\t\treturn errors.New("ConfStates not equivalent after sorting")\n')
CONFSTATE_IMPORT_UPSTREAM = '\t"fmt"\n\t"slices"\n'
CONFSTATE_IMPORT_PATCHED = '\t"errors"\n\t"slices"\n'

# file (by OUT path) -> ordered (exact-once old, new) pairs + imports to drop.
SUBJECT_PATCHES = {
    "raftpb/confstate.go": {
        "swaps": [(CONFSTATE_NIL_UPSTREAM, CONFSTATE_NIL_PATCHED),
                  (CONFSTATE_NEQ_UPSTREAM, CONFSTATE_NEQ_PATCHED),
                  (CONFSTATE_IMPORT_UPSTREAM, CONFSTATE_IMPORT_PATCHED)],
        # The fmt import is replaced by the swap above; the residue check
        # proves no `fmt.` reference survives in the code.
        "residual_free": ["fmt"],
    },
    "raft/raft.go": {
        "swaps": [(INTN_UPSTREAM, INTN_PATCHED)],
        # D-11 re-key (2026-09-30): crypto/rand -> math/rand keeps the `rand`
        # identifier bound (the residual-reference check is skipped for a
        # SWAPPED import by design: the new body's `rand.Intn` is the point);
        # math/big is dropped with the old body and stays residual-checked.
        "swap_imports": [("crypto/rand", "math/rand")],
        "drop_imports": ["math/big"],
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
    # An import SWAP (D-11 re-key, 2026-09-30): one upstream import path
    # becomes another with the SAME last element, so the patched body's
    # references stay bound; exactly once, fail closed if absent. gofmt (run
    # over the whole tree at the end) re-sorts the import block.
    for old_pkg, new_pkg in spec.get("swap_imports", []):
        if old_pkg.split("/")[-1] != new_pkg.split("/")[-1]:
            refuse("subject patch for %s: swap %r -> %r changes the bound "
                   "identifier — use drop_imports + a re-read body" % (outp, old_pkg, new_pkg))
        text, n = re.subn(r'^\t"%s"\n' % re.escape(old_pkg), '\t"%s"\n' % new_pkg, text,
                          count=1, flags=re.M)
        if not n:
            refuse("subject patch for %s: import %r to swap is not present" % (outp, old_pkg))
    # The residual-reference check ranges over CODE, not comments
    # (upstream's own doc comment above lockedRand says "rand.Rand").
    code = "\n".join(re.sub(r"//.*$", "", ln) for ln in text.split("\n"))
    for pkg in spec.get("residual_free", []):
        if re.search(r"\b%s\." % re.escape(pkg), code):
            refuse("subject patch for %s: the code still references %s. after "
                   "the patch" % (outp, pkg))
    for pkg in spec.get("drop_imports", []):
        text, n = re.subn(r'^\t(?:\w+ )?"%s"\n' % re.escape(pkg), "", text,
                          count=1, flags=re.M)
        if not n:
            refuse("subject patch for %s: import %r to drop is not present" % (outp, pkg))
        if re.search(r"\b%s\." % re.escape(pkg.split("/")[-1]), code):
            refuse("subject patch for %s: the code still references %s after "
                   "dropping its import" % (outp, pkg))
    return text, len(spec["swaps"]) + len(spec.get("swap_imports", [])) + len(spec.get("drop_imports", []))


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
        self.has_unknown = False  # the kept unknownFields []byte (D3)


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
        if ftype == "protoimpl.UnknownFields":
            # ROUTE A D3 (D-1 NARROWED): the unknown-field store is KEPT,
            # under upstream's field name, at its own type —
            # protoimpl.UnknownFields = impl.UnknownFields = []byte
            # (runtime/protoimpl/impl.go:38, internal/impl/message.go:114-
            # 115). It is not a protobuf field, so it joins no field list.
            if fname != "unknownFields" or msg.has_unknown:
                refuse("unexpected unknown-field store in %s: %r" % (msg.name, ln))
            msg.has_unknown = True
            kept.append("\tunknownFields []byte")
            continue
        if ftype in PROTOIMPL_FIELD_TYPES:
            continue  # T3: strip the protobuf runtime's private fields
        if "protoimpl" in ftype or "protoreflect" in ftype:
            refuse("unknown protobuf-runtime field type in %s: %s %s"
                   % (msg.name, fname, ftype))
        msg.fields.append((fname, ftype, ftag.strip()))
        kept.append(ln)
    kept.append("}")
    if not msg.has_unknown:
        refuse("message %s has no protoimpl.UnknownFields store — the route A "
               "codec retains unknown fields (D3); re-read the generated "
               "struct" % msg.name)
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
            # Enum String gets a REAL body (W4.3 item 1, the rendered
            # tier — docs/raft-w43-log.md): upstream's generated body is
            # protoimpl.X.EnumStringOf over the same _name map this file
            # keeps, i.e. the mapped name, else the decimal number. The
            # W2 stub was a recorded delta; this removes it. The decimal
            # fallback (unreachable for in-range values, which is every
            # value the traces carry) goes through the shared helper
            # appended at the end of the file — no strconv import, so
            # the derivation stays import-free.
            name = re.match(r"^func \(x (\w+)\)", first).group(1)
            emit = ("func (x %s) String() string {\n"
                    "\tif s, ok := %s_name[int32(x)]; ok {\n"
                    "\t\treturn s\n"
                    "\t}\n"
                    "\treturn plainpbEnumUnknown(int32(x))\n"
                    "}" % (name, name))
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

    # The enum-String fallback helper (see the enum String rule above):
    # decimal rendering of an out-of-range value, mirroring the protobuf
    # runtime's EnumStringOf fallback, digit loop so the file stays
    # import-free.
    out.append(
        "// plainpbEnumUnknown renders an out-of-range enum value the way the\n"
        "// protobuf runtime's EnumStringOf fallback does: the decimal number.\n"
        "// Unreachable for every value the name maps carry.\n"
        "func plainpbEnumUnknown(v int32) string {\n"
        "\tif v == 0 {\n"
        "\t\treturn \"0\"\n"
        "\t}\n"
        "\tneg := v < 0\n"
        "\tu := uint32(v)\n"
        "\tif neg {\n"
        "\t\tu = uint32(-int64(v))\n"
        "\t}\n"
        "\ts := \"\"\n"
        "\tfor u > 0 {\n"
        "\t\ts = string(rune('0'+int(u%10))) + s\n"
        "\t\tu /= 10\n"
        "\t}\n"
        "\tif neg {\n"
        "\t\ts = \"-\" + s\n"
        "\t}\n"
        "\treturn s\n"
        "}")

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
// Fail-closed stubs: %d (message String, Descriptor, EnumDescriptor,
// UnmarshalJSON). Enum String is REAL (W4.3 item 1): the _name map plus
// the decimal fallback, mirroring the runtime's EnumStringOf.
// Dropped: the file-descriptor machinery and ProtoReflect, and the
// runtime's private `state` and `sizeCache` fields (see the log's
// subject-delta ledger for the itemised list and the reasoning). KEPT
// since route A (D3, D-1 narrowed): `unknownFields []byte` under
// upstream's name and type (protoimpl.UnknownFields = []byte).
//
// WIRE CODEC — ROUTE A (docs/2026-10-04_route-a-protobuf-design.md): the
// generated plain_wire.go / plain_codec.go / plain_clone.go, decomposed
// after protobuf-go v1.36.11's protowire / internal/impl functions (each
// names its twin by file:line), dispatched from the subject-local proto
// package through an interface. The differential obligation is
// difftest.py sections 7-8 (vs the real protobuf runtime, exact) plus the
// codeccheck.py battery under both oracles."""


# ------------------------------------- generated codec: route A, shape A1 ----
#
# ROUTE A slice S1 (design docs/2026-10-04_route-a-protobuf-design.md, D1-D8,
# ratified [USER] Mike 2026-10-04 «Approved», relayed): a GENERATED,
# reflection-free Go codec decomposed function-for-function after
# protobuf-go v1.36.11's own `protowire` / `internal/impl` entry points, so
# every generated function names its upstream twin by file:line (the doc
# comment, and the FuncId table D8 writes to tools/raftsubject/
# codec-funcids.tsv).  Three files, all derived from the field lists parsed
# out of raft.pb.go and cross-checked against the struct tags:
#
#   raftpb/plain_wire.go    the protowire twins + the impl-level shared
#                           helpers and error values (schema-independent)
#   raftpb/plain_codec.go   per type: IsNilMessage / ResetMessage /
#                           SizeMessage / MarshalAppend /
#                           UnmarshalMessage(b, depth) / ProtoClone /
#                           ProtoEqual
#   raftpb/plain_clone.go   per type: CloneMessage (New + mergePointer) /
#                           mergeMessage / EqualMessage (equalMessage)
#
# and the subject-local `proto` package (proto/proto.go) dispatches through
# an INTERFACE (D2) — it no longer imports raftpb; raftpb imports proto, as
# upstream's generated code imports protoimpl.  Anything the rules below do
# not recognise REFUSES.
#
# D6, the generated-code grammar: plain `for` loops (three-clause or a
# single condition — never `range`, never `for {}`), no closures, no
# `goto`, no `fmt`, no reflection; recursion is bounded by protobuf-go's own
# depth counters (D4).  The field-number dispatch in each UnmarshalMessage
# is the ONE place a tagless `switch` is emitted — Q5 is PENDING with the
# logic team ([USER] relaying), so the form is ONE constant here:
# DISPATCH_FORM = "tagless-switch" | "if-chain"; flipping it regenerates
# every site (listed in codec-funcids.tsv, column `dispatch`).

PB_VERSION = "protobuf-go v1.36.11"

DISPATCH_FORM = "tagless-switch"
DISPATCH_FORMS = ("tagless-switch", "if-chain")

FUNCIDS_PATH = "tools/raftsubject/codec-funcids.tsv"

# D8: the SHA-256 of every GENERATED file, pinned.  `--check` recomputes
# them from a fresh derivation and refuses a mismatch, so an edit to the
# generator that changes emitted bytes is visible in review as a digest move
# (paste the table printed by --print-generated-digests).  The generator is
# deterministic (field-number order; no map iteration feeds the output).
GENERATED_DIGESTS = {
    "raftpb/plain_wire.go": "33bcf2bad2d9166f61a4bd8053f0a0d2c9c15d5240bc52cca9aa1bd2c7e57867",
    "raftpb/plain_codec.go": "0d5dd5367b4cff998f6c168f4a866f806efa97e98fa2a78c906d78a1f2967fd8",
    "raftpb/plain_clone.go": "9bbb04defd0cda2a24e276015a41dab9b0d838bfb384dd9cc9597d7d6c2351ec",
    "proto/proto.go": "8542e21dc8bffe6e4f559bfaf9cf7c1fb1ecebec8a13e5334fd8055e93ae2fe1",
}


def tag_bytes(num, wt):
    """protowire.EncodeTag + the varint width (= f.tagsize)."""
    tag = num << 3 | wt
    n = 1
    v = tag
    while v >= 0x80:
        v >>= 7
        n += 1
    return tag, n


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
    if not (1 <= num <= (1 << 29) - 1):
        refuse("field %s.%s: field number %d outside protowire's valid range"
               % (msg_name, fname, num))
    return kind, num


def message_fields(msgs, enums, name):
    """The message's fields as (num, fname, ftype, kind), FIELD-NUMBER order
    (impl/codec_message.go:158-160 orderedCoderFields)."""
    fields = []
    for fname, ftype, ftag in msgs[name].fields:
        kind, num = classify_field(msgs, enums, name, fname, ftype, ftag)
        fields.append((num, fname, ftype, kind))
    fields.sort()
    nums = [f[0] for f in fields]
    if len(set(nums)) != len(nums):
        refuse("duplicate field numbers in %s: %s" % (name, nums))
    return fields


# ---- plain_wire.go: schema-independent ------------------------------------
#
# Every entry: (wire key, upstream twin, footprint).  The footprint column is
# the logic team's (e): what the function reads, writes, allocates, and what
# bounds its recursion.  Kept beside the text it describes so the two cannot
# drift apart silently (the TSV is regenerated from this table + the
# per-type records below, and --check compares it).
WIRE_FUNCS = [
    ("const raftpb.{varintType..endGroupType}", "encoding/protowire/wire.go:39-46 (Type constants)", "constant"),
    ("const raftpb.{minValidNumber,maxValidNumber,defaultRecursionLimit}", "encoding/protowire/wire.go:24-29", "constant"),
    ("const raftpb.{errCodeTruncated..errCodeRecursionDepth}", "encoding/protowire/wire.go:48-56 (negative error codes)", "constant"),
    ("var raftpb.emptyBuf", "internal/impl/codec_gen.go:5703 (proto/decode_gen.go:603 in the proto twin)", "package state, zero-length, never written"),
    ("var raftpb.errDecode", "internal/impl/decode.go:19", "package state, set once at init (proto.NewError)"),
    ("var raftpb.errRecursionDepth", "internal/impl/decode.go:20", "package state, set once at init (proto.NewError)"),
    ("var raftpb.errUnknown", "internal/impl/decode.go:101", "package state, set once at init (errors.New); never returned to a caller of proto"),
    ("func raftpb.consumeVarint", "encoding/protowire/wire.go:267-367 ConsumeVarint", "pure: reads b[0:10]; loop bounded by 10"),
    ("func raftpb.sizeVarint", "encoding/protowire/wire.go:371-399 SizeVarint", "pure; loop bounded by 10"),
    ("func raftpb.appendVarint", "encoding/protowire/wire.go:185-263 AppendVarint", "allocates (append to b); loop bounded by 10"),
    ("func raftpb.encodeTag", "encoding/protowire/wire.go:534-536 EncodeTag", "pure"),
    ("func raftpb.decodeTag", "encoding/protowire/wire.go:525-531 DecodeTag", "pure"),
    ("func raftpb.appendTag", "encoding/protowire/wire.go:162-164 AppendTag", "allocates (append to b)"),
    ("func raftpb.consumeTag", "encoding/protowire/wire.go:168-178 ConsumeTag", "pure: reads b"),
    ("func raftpb.encodeBool", "encoding/protowire/wire.go:566-571 EncodeBool", "pure"),
    ("func raftpb.decodeBool", "encoding/protowire/wire.go:558-560 DecodeBool", "pure"),
    ("func raftpb.consumeFixed32", "encoding/protowire/wire.go:412-418 ConsumeFixed32 (length only; the value is never used by a skip)", "pure: reads len(b)"),
    ("func raftpb.consumeFixed64", "encoding/protowire/wire.go:440-446 ConsumeFixed64 (length only; the value is never used by a skip)", "pure: reads len(b)"),
    ("func raftpb.consumeBytes", "encoding/protowire/wire.go:460-469 ConsumeBytes", "pure: reads b; result aliases b"),
    ("func raftpb.appendBytes", "encoding/protowire/wire.go:454-456 AppendBytes", "allocates (append to b); reads v"),
    ("func raftpb.sizeBytes", "encoding/protowire/wire.go:473-475 SizeBytes", "pure"),
    ("func raftpb.consumeFieldValue", "encoding/protowire/wire.go:112-114 ConsumeFieldValue", "pure: reads b; recursion via consumeFieldValueD"),
    ("func raftpb.consumeFieldValueD", "encoding/protowire/wire.go:116-160 consumeFieldValueD", "pure: reads b; recursion bounded by depth (defaultRecursionLimit, -1 per nested group); loop consumes >= 1 byte per iteration"),
    ("func raftpb.consumeField", "encoding/protowire/wire.go:94-105 ConsumeField", "pure: reads b"),
    ("func raftpb.bytesEqual", "go1.26.5 bytes.Equal (src/bytes/bytes.go) — as called by impl/equal.go:197", "pure: reads a, b"),
    ("func raftpb.unknownFieldRecords", "internal/impl/equal.go:205-209 (the per-field-number accumulation mx[fnum] = append(mx[fnum], x[:n]...), map-free)", "allocates (the concatenation); reads x"),
    ("func raftpb.equalUnknown", "internal/impl/equal.go:193-224 equalUnknown", "allocates (per-number concatenations); reads x, y"),
    ("func raftpb.consumeVarintValue", "internal/impl/codec_gen.go:2762-2780 (the shared head of consumeUint64Ptr; = :108-124 consumeBoolPtr, :687-703 consumeInt32Ptr — coderEnumPtr = coderInt32Ptr, codec_unsafe.go:12)", "pure: reads b"),
    ("func raftpb.consumeBytesValue", "internal/impl/codec_gen.go:5410-5417 (the shared head of consumeBytes; = codec_field.go:175-182 consumeMessageInfo, :438-445 consumeMessageSliceInfo)", "pure: reads b; result aliases b"),
    ("func raftpb.consumePackedUint64", "internal/impl/codec_gen.go:2818-2850 (the packed branch of consumeUint64Slice)", "allocates (append to s); reads b; loop consumes >= 1 byte per iteration"),
]


WIRE_GO = '''// Code GENERATED by tools/raftsubject/derive.py. DO NOT EDIT — edit the
// derivation.
//
// ROUTE A (docs/2026-10-04_route-a-protobuf-design.md, D1): the protowire
// twins and the impl-level shared helpers of the plainpb codec, each named
// after its %(pb)s twin by file:line (paths relative to the
// module root google.golang.org/protobuf@v1.36.11). The FuncId table with
// the footprint of every function here is tools/raftsubject/codec-funcids.tsv.
//
// Plain Go: no reflection, no unsafe, no fmt, no closures, no `range`.
// Recursion (the group skipper) is bounded by protowire's own depth counter.

package raftpb

import (
	"errors"

	"proto"
)

// protowire.Type — encoding/protowire/wire.go:39-46.
const (
	varintType     = 0
	fixed64Type    = 1
	bytesType      = 2
	startGroupType = 3
	endGroupType   = 4
	fixed32Type    = 5
)

// encoding/protowire/wire.go:24-29.
const (
	minValidNumber        = 1
	maxValidNumber        = 1<<29 - 1
	defaultRecursionLimit = 10000
)

// The negative error codes — encoding/protowire/wire.go:48-56. The impl
// layer collapses every one of them to errDecode (impl/decode.go:19).
const (
	errCodeTruncated      = -1
	errCodeFieldNumber    = -2
	errCodeOverflow       = -3
	errCodeReserved       = -4
	errCodeEndGroup       = -5
	errCodeRecursionDepth = -6
)

// emptyBuf — internal/impl/codec_gen.go:5703: appending to emptyBuf[:]
// yields a NON-nil slice even for zero bytes (proto2 bytes presence).
var emptyBuf [0]byte

// errDecode — internal/impl/decode.go:19: the ONE value every malformation
// returns (a *prefixError: «proto: cannot parse invalid wire-format data»,
// the prefix spelled per the proto package's init pick).
var errDecode = proto.NewError("cannot parse invalid wire-format data")

// errRecursionDepth — internal/impl/decode.go:20 (D4: reachable for a
// raftpb client through Message.responses nested past 10000 messages).
var errRecursionDepth = proto.NewError("exceeded maximum recursion depth")

// errUnknown — internal/impl/decode.go:101: the in-band sentinel a field
// consumer returns for a WRONG wire type; the decode loop turns it into
// unknown-field retention. Never returned to a caller of proto.Unmarshal.
var errUnknown = errors.New("unknown")

// consumeVarint — encoding/protowire/wire.go:267-367 ConsumeVarint (the
// unrolled ten steps as one bounded loop): at most 10 bytes, the 10th < 2
// (errCodeOverflow), errCodeTruncated when b ends first.
func consumeVarint(b []byte) (uint64, int) {
	var v uint64
	for i := 0; i < 10; i++ {
		if len(b) <= i {
			return 0, errCodeTruncated
		}
		y := uint64(b[i])
		if i == 9 {
			v += y << 63
			if y < 2 {
				return v, 10
			}
			return 0, errCodeOverflow
		}
		v += y << (7 * uint(i))
		if y < 0x80 {
			return v, i + 1
		}
		v -= uint64(0x80) << (7 * uint(i))
	}
	return 0, errCodeOverflow
}

// sizeVarint — encoding/protowire/wire.go:371-399 SizeVarint: 1..10.
func sizeVarint(v uint64) int {
	n := 1
	for i := 0; i < 9; i++ {
		if v < 0x80 {
			break
		}
		v >>= 7
		n++
	}
	return n
}

// appendVarint — encoding/protowire/wire.go:185-263 AppendVarint.
func appendVarint(b []byte, v uint64) []byte {
	for i := 0; i < 9; i++ {
		if v < 0x80 {
			break
		}
		b = append(b, byte(v&0x7f|0x80))
		v >>= 7
	}
	return append(b, byte(v))
}

// encodeTag — encoding/protowire/wire.go:534-536 EncodeTag.
func encodeTag(num int32, typ int) uint64 {
	return uint64(num)<<3 | uint64(typ&7)
}

// decodeTag — encoding/protowire/wire.go:525-531 DecodeTag: a field number
// above MaxInt32 decodes to -1.
func decodeTag(x uint64) (int32, int) {
	if x>>3 > 0x7fffffff {
		return -1, 0
	}
	return int32(x >> 3), int(x & 7)
}

// appendTag — encoding/protowire/wire.go:162-164 AppendTag (the CANONICAL
// re-encoding: a non-minimal tag on the wire is retained minimal).
func appendTag(b []byte, num int32, typ int) []byte {
	return appendVarint(b, encodeTag(num, typ))
}

// consumeTag — encoding/protowire/wire.go:168-178 ConsumeTag: refuses only
// num < 1 — so INSIDE a skipped group a field number in [2^29, 2^31) is
// accepted, where the message loop (impl/decode.go:149-155) refuses it.
func consumeTag(b []byte) (int32, int, int) {
	v, n := consumeVarint(b)
	if n < 0 {
		return 0, 0, n
	}
	num, typ := decodeTag(v)
	if num < minValidNumber {
		return 0, 0, errCodeFieldNumber
	}
	return num, typ, n
}

// encodeBool — encoding/protowire/wire.go:566-571 EncodeBool.
func encodeBool(x bool) uint64 {
	if x {
		return 1
	}
	return 0
}

// decodeBool — encoding/protowire/wire.go:558-560 DecodeBool.
func decodeBool(x uint64) bool {
	return x != 0
}

// consumeFixed32 — encoding/protowire/wire.go:412-418 ConsumeFixed32
// (the length half; a skip never reads the value).
func consumeFixed32(b []byte) int {
	if len(b) < 4 {
		return errCodeTruncated
	}
	return 4
}

// consumeFixed64 — encoding/protowire/wire.go:440-446 ConsumeFixed64
// (the length half; a skip never reads the value).
func consumeFixed64(b []byte) int {
	if len(b) < 8 {
		return errCodeTruncated
	}
	return 8
}

// consumeBytes — encoding/protowire/wire.go:460-469 ConsumeBytes: the
// length-prefixed value, ALIASING b (callers copy where upstream copies).
func consumeBytes(b []byte) ([]byte, int) {
	m, n := consumeVarint(b)
	if n < 0 {
		return nil, n
	}
	if m > uint64(len(b)-n) {
		return nil, errCodeTruncated
	}
	return b[n : n+int(m)], n + int(m)
}

// appendBytes — encoding/protowire/wire.go:454-456 AppendBytes.
func appendBytes(b []byte, v []byte) []byte {
	b = appendVarint(b, uint64(len(v)))
	return append(b, v...)
}

// sizeBytes — encoding/protowire/wire.go:473-475 SizeBytes.
func sizeBytes(n int) int {
	return sizeVarint(uint64(n)) + n
}

// consumeFieldValue — encoding/protowire/wire.go:112-114 ConsumeFieldValue.
func consumeFieldValue(num int32, typ int, b []byte) int {
	return consumeFieldValueD(num, typ, b, defaultRecursionLimit)
}

// consumeFieldValueD — encoding/protowire/wire.go:116-160: wire types
// 0/1/2/5 by size; 3 skips tag/value pairs recursively (depth-1 per level,
// errCodeRecursionDepth below 0) up to the matching end tag
// (errCodeEndGroup on a mismatch); 4 alone is errCodeEndGroup; 6/7 are
// errCodeReserved. Upstream's `for {}` is the `for len(b) > 0` loop here,
// with the empty-input exit made explicit: ConsumeTag on empty input is
// errCodeTruncated, exactly the value returned after the loop.
func consumeFieldValueD(num int32, typ int, b []byte, depth int) int {
	if typ == varintType {
		_, n := consumeVarint(b)
		return n
	}
	if typ == fixed32Type {
		return consumeFixed32(b)
	}
	if typ == fixed64Type {
		return consumeFixed64(b)
	}
	if typ == bytesType {
		_, n := consumeBytes(b)
		return n
	}
	if typ == startGroupType {
		if depth < 0 {
			return errCodeRecursionDepth
		}
		n0 := len(b)
		for len(b) > 0 {
			num2, typ2, n := consumeTag(b)
			if n < 0 {
				return n
			}
			b = b[n:]
			if typ2 == endGroupType {
				if num != num2 {
					return errCodeEndGroup
				}
				return n0 - len(b)
			}
			m := consumeFieldValueD(num2, typ2, b, depth-1)
			if m < 0 {
				return m
			}
			b = b[m:]
		}
		return errCodeTruncated
	}
	if typ == endGroupType {
		return errCodeEndGroup
	}
	return errCodeReserved
}

// consumeField — encoding/protowire/wire.go:94-105 ConsumeField: the whole
// record (tag + value, an end-group marker included).
func consumeField(b []byte) (int32, int, int) {
	num, typ, n := consumeTag(b)
	if n < 0 {
		return 0, 0, n
	}
	m := consumeFieldValue(num, typ, b[n:])
	if m < 0 {
		return 0, 0, m
	}
	return num, typ, n + m
}

// bytesEqual — bytes.Equal (go1.26.5 src/bytes/bytes.go) as impl/equal.go
// calls it: equal lengths and equal bytes; nil equals empty.
func bytesEqual(a, b []byte) bool {
	if len(a) != len(b) {
		return false
	}
	for i := 0; i < len(a); i++ {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

// unknownFieldRecords — the per-field-number accumulation of
// internal/impl/equal.go:205-209 (mx[fnum] = append(mx[fnum], x[:n]...)),
// map-free: the raw records of x whose number is num, concatenated in
// arrival order. x is retained unknown bytes, well-formed by construction
// (the decode loop validated every record); a negative n would slice-panic
// here exactly as upstream's x[:n] does.
func unknownFieldRecords(x []byte, num int32) []byte {
	var out []byte
	for len(x) > 0 {
		fnum, _, n := consumeField(x)
		if fnum == num {
			out = append(out, x[:n]...)
		}
		x = x[n:]
	}
	return out
}

// equalUnknown — internal/impl/equal.go:193-224 equalUnknown: equal length
// AND (byte-equal OR, per field number, equal concatenations of that
// number's records in arrival order, over the same set of numbers).
func equalUnknown(x, y []byte) bool {
	if len(x) != len(y) {
		return false
	}
	if bytesEqual(x, y) {
		return true
	}
	rest := x
	for len(rest) > 0 {
		fnum, _, n := consumeField(rest)
		if !bytesEqual(unknownFieldRecords(x, fnum), unknownFieldRecords(y, fnum)) {
			return false
		}
		rest = rest[n:]
	}
	rest = y
	for len(rest) > 0 {
		fnum, _, n := consumeField(rest)
		if len(unknownFieldRecords(x, fnum)) == 0 {
			return false
		}
		rest = rest[n:]
	}
	return true
}

// consumeVarintValue — internal/impl/codec_gen.go:2762-2780, the shared
// head of consumeUint64Ptr (= :108-124 consumeBoolPtr, :687-703
// consumeInt32Ptr, which IS the enum coder): a wrong wire type is
// errUnknown (retained as an unknown field), a malformed value errDecode;
// the 1-byte and 2-byte fast paths are upstream's.
func consumeVarintValue(b []byte, wtyp int) (uint64, int, error) {
	if wtyp != varintType {
		return 0, 0, errUnknown
	}
	var v uint64
	var n int
	if len(b) >= 1 && b[0] < 0x80 {
		v = uint64(b[0])
		n = 1
	} else if len(b) >= 2 && b[1] < 128 {
		v = uint64(b[0]&0x7f) + uint64(b[1])<<7
		n = 2
	} else {
		v, n = consumeVarint(b)
	}
	if n < 0 {
		return 0, 0, errDecode
	}
	return v, n, nil
}

// consumeBytesValue — internal/impl/codec_gen.go:5410-5417, the shared head
// of consumeBytes (= codec_field.go:175-182 consumeMessageInfo, :438-445
// consumeMessageSliceInfo): wrong wire type errUnknown, malformed errDecode.
func consumeBytesValue(b []byte, wtyp int) ([]byte, int, error) {
	if wtyp != bytesType {
		return nil, 0, errUnknown
	}
	v, n := consumeBytes(b)
	if n < 0 {
		return nil, 0, errDecode
	}
	return v, n, nil
}

// consumePackedUint64 — internal/impl/codec_gen.go:2818-2850, the PACKED
// branch of consumeUint64Slice: accepted although never emitted. (Upstream
// pre-grows the slice by the element count — a capacity-only effect, not
// reproduced.) On error s is returned unextended, as upstream stores *sp
// only on success.
func consumePackedUint64(b []byte, s []uint64) ([]uint64, int, error) {
	p, n := consumeBytes(b)
	if n < 0 {
		return s, 0, errDecode
	}
	out := s
	for len(p) > 0 {
		var v uint64
		var k int
		if len(p) >= 1 && p[0] < 0x80 {
			v = uint64(p[0])
			k = 1
		} else if len(p) >= 2 && p[1] < 128 {
			v = uint64(p[0]&0x7f) + uint64(p[1])<<7
			k = 2
		} else {
			v, k = consumeVarint(p)
		}
		if k < 0 {
			return s, 0, errDecode
		}
		out = append(out, v)
		p = p[k:]
	}
	return out, n, nil
}
''' % {"pb": PB_VERSION}


def gen_wire():
    return WIRE_GO


# ---- the per-type codec (plain_codec.go) -----------------------------------

CODEC_HEADER = """// Code GENERATED by tools/raftsubject/derive.py from the message field
// lists parsed out of raft.pb.go, cross-checked against the struct tags
// (wire type, field number, opt/rep mode). DO NOT EDIT — edit the
// derivation.
//
// ROUTE A (docs/2026-10-04_route-a-protobuf-design.md, D1/D2/D4): per
// message type, the methods the proto package dispatches to through its
// `methods` interface, each the twin of a %(pb)s
// internal/impl entry point (file:line in each doc comment; the FuncId
// table: tools/raftsubject/codec-funcids.tsv):
//
//   IsNilMessage()          !ProtoReflect().IsValid()   (a typed nil)
//   ResetMessage()          the generated Reset's plain-Go half
//   SizeMessage() int       impl/encode.go:47 sizePointer
//   MarshalAppend(b) []byte impl/encode.go:148 marshalAppendPointer
//   UnmarshalMessage(b, d)  impl/decode.go:103 unmarshalPointer + :124
//                           unmarshalPointerEager (d = remaining depth)
//   ProtoClone() Message    proto/merge.go:41 Clone (New + mergePointer)
//   ProtoEqual(Message)     impl/equal.go:22 equalMessage
//
// Encoding: fields in FIELD-NUMBER order, proto2 presence, repeated
// varints UNPACKED, the retained unknown bytes LAST. Decoding: merge
// semantics, last-one-wins scalars REUSING the cell, embedded messages
// merge, repeated fields append, packed varints accepted, a WRONG wire
// type on a known field and every unknown field RETAINED in
// unknownFields (canonical tag + raw value, arrival order), every
// malformation the one errDecode value, nesting past 10000 messages
// errRecursionDepth.

package raftpb

import "proto"
""" % {"pb": PB_VERSION}


def _dispatch(arms, indent):
    """Render the field-number dispatch: arms = [(cond, [body lines])].
    The ONLY tagless-switch site of the generator (Q5 PENDING)."""
    t = "\t" * indent
    out = []
    if DISPATCH_FORM == "tagless-switch":
        out.append(t + "switch {")
        for cond, body in arms:
            out.append(t + "case %s:" % cond)
            out += [t + "\t" + ln for ln in body]
        out.append(t + "}")
    elif DISPATCH_FORM == "if-chain":
        for k, (cond, body) in enumerate(arms):
            out.append(t + ("if %s {" % cond if k == 0 else "} else if %s {" % cond))
            out += [t + "\t" + ln for ln in body]
        if arms:
            out.append(t + "}")
    else:
        refuse("DISPATCH_FORM %r is not one of %s" % (DISPATCH_FORM, DISPATCH_FORMS))
    return out


def gen_codec(msgs, enums, records):
    out = [CODEC_HEADER]
    for name in msgs:
        fields = message_fields(msgs, enums, name)
        recv = "(*raftpb.%s)" % name

        # ---- IsNilMessage / ResetMessage ---------------------------------
        out.append("\n".join([
            "// IsNilMessage reports a TYPED-NIL message — the negation of",
            "// ProtoReflect().IsValid() for a generated message (proto/encode.go:141-146",
            "// emptyBytesForMessage, proto/merge.go:55-57 Clone, proto/equal.go:52-54 Equal).",
            "func (x *%s) IsNilMessage() bool {" % name,
            "\treturn x == nil",
            "}"]))
        records.append(("method %s.IsNilMessage" % recv,
                        "protoreflect.Message.IsValid on a generated message (internal/impl/message_reflect.go messageState/messageReflectWrapper)",
                        "pure: reads the receiver pointer", "-"))
        out.append("\n".join([
            "// ResetMessage is the generated Reset's plain-Go half (raft.pb.go",
            "// `*x = %s{}`; proto/reset.go:16-22 calls it). A typed-nil receiver" % name,
            "// nil-dereferences, as upstream's does.",
            "func (x *%s) ResetMessage() {" % name,
            "\t*x = %s{}" % name,
            "}"]))
        records.append(("method %s.ResetMessage" % recv,
                        "raft.pb.go generated Reset (the `*x = T{}` half) via proto/reset.go:16-22",
                        "writes *x (every field, unknownFields included)", "-"))

        # ---- SizeMessage -------------------------------------------------
        s = ["// SizeMessage — internal/impl/encode.go:47-61 sizePointer + :63-132",
             "// sizePointerSlow: a nil receiver sizes 0; per present field tagsize +",
             "// value size in field-number order; plus len(unknownFields).",
             "func (x *%s) SizeMessage() int {" % name,
             "\tif x == nil {",
             "\t\treturn 0",
             "\t}",
             "\tn := 0"]
        for num, fname, ftype, kind in fields:
            wt = 2 if kind in ("bytes", "msg", "rep-msg") else 0
            _tag, ts = tag_bytes(num, wt)
            if kind == "scalar-u64":
                s += ["\tif x.%s != nil {" % fname,
                      "\t\tn += %d + sizeVarint(*x.%s)" % (ts, fname),
                      "\t}"]
            elif kind == "scalar-bool":
                s += ["\tif x.%s != nil {" % fname,
                      "\t\tn += %d + sizeVarint(encodeBool(*x.%s))" % (ts, fname),
                      "\t}"]
            elif kind == "scalar-enum":
                s += ["\tif x.%s != nil {" % fname,
                      "\t\tn += %d + sizeVarint(uint64(*x.%s))" % (ts, fname),
                      "\t}"]
            elif kind == "bytes":
                s += ["\tif x.%s != nil {" % fname,
                      "\t\tn += %d + sizeBytes(len(x.%s))" % (ts, fname),
                      "\t}"]
            elif kind == "msg":
                s += ["\tif x.%s != nil {" % fname,
                      "\t\tn += %d + sizeBytes(x.%s.SizeMessage())" % (ts, fname),
                      "\t}"]
            elif kind == "rep-u64":
                s += ["\tfor i := 0; i < len(x.%s); i++ {" % fname,
                      "\t\tn += %d + sizeVarint(x.%s[i])" % (ts, fname),
                      "\t}"]
            elif kind == "rep-msg":
                s += ["\tfor i := 0; i < len(x.%s); i++ {" % fname,
                      "\t\tn += %d + sizeBytes(x.%s[i].SizeMessage())" % (ts, fname),
                      "\t}"]
        s += ["\tn += len(x.unknownFields)", "\treturn n", "}"]
        out.append("\n".join(s))
        records.append(("method %s.SizeMessage" % recv,
                        "internal/impl/encode.go:47-61 sizePointer, :63-132 sizePointerSlow; codec_gen.go sizeUint64Ptr :2747 / sizeBoolPtr :93 / sizeInt32Ptr :672 / sizeUint64Slice :2797 / sizeBytes :5396; codec_field.go sizeMessageInfo :159 / sizeMessageSliceInfo :410",
                        "pure: reads *x (recursively the embedded messages); recursion bounded by the value's finite nesting", "-"))

        # ---- MarshalAppend -----------------------------------------------
        a = ["// MarshalAppend — internal/impl/encode.go:148-226 marshalAppendPointer:",
             "// a nil receiver appends nothing; present fields in field-number order;",
             "// the retained unknown bytes LAST. Marshal cannot fail on these schemas",
             "// (no required field, no UTF-8 check; the size-mismatch error of",
             "// codec_field.go:169-171 needs a concurrent mutation).",
             "func (x *%s) MarshalAppend(b []byte) []byte {" % name,
             "\tif x == nil {",
             "\t\treturn b",
             "\t}"]
        for num, fname, ftype, kind in fields:
            wt = 2 if kind in ("bytes", "msg", "rep-msg") else 0
            tag, _ts = tag_bytes(num, wt)
            if kind == "scalar-u64":
                a += ["\tif x.%s != nil {" % fname,
                      "\t\tb = appendVarint(b, 0x%x)" % tag,
                      "\t\tb = appendVarint(b, *x.%s)" % fname,
                      "\t}"]
            elif kind == "scalar-bool":
                a += ["\tif x.%s != nil {" % fname,
                      "\t\tb = appendVarint(b, 0x%x)" % tag,
                      "\t\tb = appendVarint(b, encodeBool(*x.%s))" % fname,
                      "\t}"]
            elif kind == "scalar-enum":
                a += ["\tif x.%s != nil {" % fname,
                      "\t\tb = appendVarint(b, 0x%x)" % tag,
                      "\t\tb = appendVarint(b, uint64(*x.%s))" % fname,
                      "\t}"]
            elif kind == "bytes":
                a += ["\tif x.%s != nil {" % fname,
                      "\t\tb = appendVarint(b, 0x%x)" % tag,
                      "\t\tb = appendBytes(b, x.%s)" % fname,
                      "\t}"]
            elif kind == "msg":
                a += ["\tif x.%s != nil {" % fname,
                      "\t\tsiz := x.%s.SizeMessage()" % fname,
                      "\t\tb = appendVarint(b, 0x%x)" % tag,
                      "\t\tb = appendVarint(b, uint64(siz))",
                      "\t\tb = x.%s.MarshalAppend(b)" % fname,
                      "\t}"]
            elif kind == "rep-u64":
                a += ["\tfor i := 0; i < len(x.%s); i++ {" % fname,
                      "\t\tb = appendVarint(b, 0x%x)" % tag,
                      "\t\tb = appendVarint(b, x.%s[i])" % fname,
                      "\t}"]
            elif kind == "rep-msg":
                a += ["\tfor i := 0; i < len(x.%s); i++ {" % fname,
                      "\t\tb = appendVarint(b, 0x%x)" % tag,
                      "\t\tsiz := x.%s[i].SizeMessage()" % fname,
                      "\t\tb = appendVarint(b, uint64(siz))",
                      "\t\tb = x.%s[i].MarshalAppend(b)" % fname,
                      "\t}"]
        a += ["\tb = append(b, x.unknownFields...)", "\treturn b", "}"]
        out.append("\n".join(a))
        records.append(("method %s.MarshalAppend" % recv,
                        "internal/impl/encode.go:148-226 marshalAppendPointer; codec_gen.go appendUint64Ptr :2754 / appendBoolPtr :100 / appendInt32Ptr :679 / appendUint64Slice :2806 / appendBytes :5402; codec_field.go appendMessageInfo :163 / appendMessageSliceInfo :419",
                        "allocates (append to b); reads *x (recursively); recursion bounded by the value's finite nesting", "-"))

        # ---- UnmarshalMessage --------------------------------------------
        arms = []
        for num, fname, ftype, kind in fields:
            base = ftype.lstrip("*[]")
            cond = "num == %d" % num
            if kind in ("scalar-u64", "scalar-bool", "scalar-enum"):
                store = {"scalar-u64": "v",
                         "scalar-bool": "decodeBool(v)",
                         "scalar-enum": "%s(int32(v))" % base}[kind]
                cell = {"scalar-u64": "uint64", "scalar-bool": "bool",
                        "scalar-enum": base}[kind]
                arms.append((cond, [
                    "v, m, e := consumeVarintValue(b, wtyp)",
                    "n = m",
                    "err = e",
                    "if e == nil {",
                    "\tif x.%s == nil {" % fname,
                    "\t\tx.%s = new(%s)" % (fname, cell),
                    "\t}",
                    "\t*x.%s = %s" % (fname, store),
                    "}"]))
            elif kind == "bytes":
                arms.append((cond, [
                    "v, m, e := consumeBytesValue(b, wtyp)",
                    "n = m",
                    "err = e",
                    "if e == nil {",
                    "\tx.%s = append(emptyBuf[:], v...)" % fname,
                    "}"]))
            elif kind == "msg":
                arms.append((cond, [
                    "v, m, e := consumeBytesValue(b, wtyp)",
                    "n = m",
                    "err = e",
                    "if e == nil {",
                    "\tif x.%s == nil {" % fname,
                    "\t\tx.%s = &%s{}" % (fname, base),
                    "\t}",
                    "\tif e2 := x.%s.UnmarshalMessage(v, depth); e2 != nil {" % fname,
                    "\t\treturn e2",
                    "\t}",
                    "}"]))
            elif kind == "rep-u64":
                arms.append((cond, [
                    "if wtyp == bytesType {",
                    "\ts, m, e := consumePackedUint64(b, x.%s)" % fname,
                    "\tn = m",
                    "\terr = e",
                    "\tif e == nil {",
                    "\t\tx.%s = s" % fname,
                    "\t}",
                    "} else {",
                    "\tv, m, e := consumeVarintValue(b, wtyp)",
                    "\tn = m",
                    "\terr = e",
                    "\tif e == nil {",
                    "\t\tx.%s = append(x.%s, v)" % (fname, fname),
                    "\t}",
                    "}"]))
            elif kind == "rep-msg":
                arms.append((cond, [
                    "v, m, e := consumeBytesValue(b, wtyp)",
                    "n = m",
                    "err = e",
                    "if e == nil {",
                    "\tel := &%s{}" % base,
                    "\tif e2 := el.UnmarshalMessage(v, depth); e2 != nil {",
                    "\t\treturn e2",
                    "\t}",
                    "\tx.%s = append(x.%s, el)" % (fname, fname),
                    "}"]))
        u = ["// UnmarshalMessage parses b and MERGES into x — internal/impl/decode.go",
             "// :103-106 unmarshalPointer (the depth counter: decremented on entry,",
             "// errRecursionDepth below 0; proto.Unmarshal passes 10000, an embedded",
             "// message the caller's decremented value) + :124-241",
             "// unmarshalPointerEager (the tag fast paths, the field-number bounds,",
             "// the end-group check — groupTag is 0 for a message, so ANY end-group",
             "// tag mismatches —, the field consumers, unknown-field retention).",
             "func (x *%s) UnmarshalMessage(b []byte, depth int) error {" % name,
             "\tdepth--",
             "\tif depth < 0 {",
             "\t\treturn errRecursionDepth",
             "\t}",
             "\tfor len(b) > 0 {",
             "\t\tvar tag uint64",
             "\t\tif b[0] < 0x80 {",
             "\t\t\ttag = uint64(b[0])",
             "\t\t\tb = b[1:]",
             "\t\t} else if len(b) >= 2 && b[1] < 128 {",
             "\t\t\ttag = uint64(b[0]&0x7f) + uint64(b[1])<<7",
             "\t\t\tb = b[2:]",
             "\t\t} else {",
             "\t\t\tv, k := consumeVarint(b)",
             "\t\t\tif k < 0 {",
             "\t\t\t\treturn errDecode",
             "\t\t\t}",
             "\t\t\ttag = v",
             "\t\t\tb = b[k:]",
             "\t\t}",
             "\t\tfn := tag >> 3",
             "\t\tif fn < minValidNumber || fn > maxValidNumber {",
             "\t\t\treturn errDecode",
             "\t\t}",
             "\t\tnum := int32(fn)",
             "\t\twtyp := int(tag & 7)",
             "\t\tif wtyp == endGroupType {",
             "\t\t\treturn errDecode",
             "\t\t}",
             "\t\tn := 0",
             "\t\terr := errUnknown"]
        u += _dispatch(arms, 2)
        u += ["\t\tif err != nil {",
              "\t\t\tif err != errUnknown {",
              "\t\t\t\treturn err",
              "\t\t\t}",
              "\t\t\tn = consumeFieldValue(num, wtyp, b)",
              "\t\t\tif n < 0 {",
              "\t\t\t\treturn errDecode",
              "\t\t\t}",
              "\t\t\tx.unknownFields = appendTag(x.unknownFields, num, wtyp)",
              "\t\t\tx.unknownFields = append(x.unknownFields, b[:n]...)",
              "\t\t}",
              "\t\tb = b[n:]",
              "\t}",
              "\treturn nil",
              "}"]
        out.append("\n".join(u))
        records.append(("method %s.UnmarshalMessage" % recv,
                        "internal/impl/decode.go:103-120 unmarshalPointer, :124-241 unmarshalPointerEager; consumers codec_gen.go consumeUint64Ptr :2762 / consumeBoolPtr :108 / consumeInt32Ptr :687 / consumeUint64Slice :2816 / consumeBytes :5410, codec_field.go consumeMessageInfo :175 / consumeMessageSliceInfo :438",
                        "reads b; writes x's fields (allocating cells, slices and embedded messages) and x.unknownFields; recursion bounded by depth (10000 from proto.Unmarshal, -1 per embedded message); the loop consumes >= 1 byte per iteration",
                        DISPATCH_FORM))

        # ---- ProtoClone / ProtoEqual -------------------------------------
        out.append("\n".join([
            "// ProtoClone — proto/merge.go:41-60 Clone past its nil-interface and",
            "// validity arms (the proto package keeps those): New + mergePointer, i.e.",
            "// CloneMessage. A typed-nil receiver answers the typed nil.",
            "func (x *%s) ProtoClone() proto.Message {" % name,
            "\treturn x.CloneMessage()",
            "}"]))
        records.append(("method %s.ProtoClone" % recv,
                        "proto/merge.go:41-60 Clone (dst := src.New(); mergeMessage)",
                        "allocates (the deep copy); reads *x (recursively)", "-"))
        out.append("\n".join([
            "// ProtoEqual — the generated fast path internal/impl/equal.go:22-27",
            "// equalMessage: a different message type is unequal (the descriptor",
            "// check); same type compares by EqualMessage.",
            "func (x *%s) ProtoEqual(m proto.Message) bool {" % name,
            "\ty, ok := m.(*%s)" % name,
            "\tif !ok {",
            "\t\treturn false",
            "\t}",
            "\treturn x.EqualMessage(y)",
            "}"]))
        records.append(("method %s.ProtoEqual" % recv,
                        "internal/impl/equal.go:22-27 equalMessage (the descriptor check) -> EqualMessage",
                        "pure: reads *x, *y (recursively)", "-"))
    return "\n\n".join(out) + "\n"


# ---- clone (merge) / equality (plain_clone.go) ------------------------------

CLONE_HEADER = """// Code GENERATED by tools/raftsubject/derive.py from the message field
// lists parsed out of raft.pb.go. DO NOT EDIT — edit the derivation.
//
// ROUTE A (docs/2026-10-04_route-a-protobuf-design.md): the typed halves
// of proto.Clone and proto.Equal, twins of %(pb)s internal/impl:
//
//   (x *T) CloneMessage() *T     proto/merge.go:41-60 Clone = New +
//                                impl/merge.go:36-113 mergePointer
//   (x *T) mergeMessage(src *T)  impl/merge.go:36-113 mergePointer
//   (x *T) EqualMessage(y *T)    impl/equal.go:22-132 equalMessage, ending
//                                in equalUnknown (:193-224)
//
// proto2 presence: an optional scalar/bytes field is SET iff its pointer
// (or, for bytes, its slice) is non-nil; a repeated field has no presence
// (nil and empty are equal; an empty one clones to nil); a NIL ELEMENT of
// a repeated message field clones to an EMPTY message
// (impl/merge.go:175-185: mergePointer from a nil src is a no-op) and
// compares equal to an empty message (the invalid element takes
// protoreflect's slow path, which ranges over no fields). Retained
// unknown bytes clone by append (impl/merge.go:106-111) and compare by
// equalUnknown.

package raftpb
""" % {"pb": PB_VERSION}


def gen_clone(msgs, enums, records):
    out = [CLONE_HEADER]
    for name in msgs:
        fields = message_fields(msgs, enums, name)
        recv = "(*raftpb.%s)" % name
        out.append("\n".join([
            "// CloneMessage — proto.Clone's New + mergePointer: a deep copy. A nil",
            "// receiver clones to nil (proto.Clone of a typed nil is the typed nil).",
            "func (x *%s) CloneMessage() *%s {" % (name, name),
            "\tif x == nil {",
            "\t\treturn nil",
            "\t}",
            "\tout := &%s{}" % name,
            "\tout.mergeMessage(x)",
            "\treturn out",
            "}"]))
        records.append(("method %s.CloneMessage" % recv,
                        "proto/merge.go:41-60 Clone (New + mergeOptions.mergeMessage)",
                        "allocates (the deep copy); reads *x (recursively)", "-"))
        mm = ["// mergeMessage — internal/impl/merge.go:36-113 mergePointer: a nil src is",
              "// a no-op; per present src field: scalars into a FRESH cell",
              "// (merge_gen.go:122 mergeUint64Ptr), bytes as append(emptyBuf[:], ...)",
              "// (merge.go:187 mergeBytes), embedded messages merged into an",
              "// allocated-if-nil destination (:159 mergeMessage), repeated fields",
              "// appended (merge_gen.go:130 mergeUint64Slice; merge.go:175",
              "// mergeMessageSlice — a fresh message per element), and src's",
              "// unknown bytes appended when non-empty (:106-111).",
              "func (x *%s) mergeMessage(src *%s) {" % (name, name),
              "\tif src == nil {",
              "\t\treturn",
              "\t}"]
        e = ["// EqualMessage — internal/impl/equal.go:22-132 equalMessage over two",
             "// messages of this type: presence must agree per field, values compare",
             "// equal, then equalUnknown. Two nil messages are equal; nil and",
             "// non-nil are not (proto.Equal checks validity first).",
             "func (x *%s) EqualMessage(y *%s) bool {" % (name, name),
             "\tif x == nil || y == nil {",
             "\t\treturn x == nil && y == nil",
             "\t}"]
        for num, fname, ftype, kind in fields:
            base = ftype.lstrip("*[]")
            if kind in ("scalar-u64", "scalar-bool", "scalar-enum"):
                mm += ["\tif src.%s != nil {" % fname,
                       "\t\tv := *src.%s" % fname,
                       "\t\tx.%s = &v" % fname,
                       "\t}"]
                e += ["\tif (x.%s == nil) != (y.%s == nil) {" % (fname, fname),
                      "\t\treturn false",
                      "\t}",
                      "\tif x.%s != nil && *x.%s != *y.%s {" % (fname, fname, fname),
                      "\t\treturn false",
                      "\t}"]
            elif kind == "bytes":
                mm += ["\tif src.%s != nil {" % fname,
                       "\t\tx.%s = append(emptyBuf[:], src.%s...)" % (fname, fname),
                       "\t}"]
                e += ["\tif (x.%s == nil) != (y.%s == nil) {" % (fname, fname),
                      "\t\treturn false",
                      "\t}",
                      "\tif !bytesEqual(x.%s, y.%s) {" % (fname, fname),
                      "\t\treturn false",
                      "\t}"]
            elif kind == "msg":
                mm += ["\tif src.%s != nil {" % fname,
                       "\t\tif x.%s == nil {" % fname,
                       "\t\t\tx.%s = &%s{}" % (fname, base),
                       "\t\t}",
                       "\t\tx.%s.mergeMessage(src.%s)" % (fname, fname),
                       "\t}"]
                e += ["\tif (x.%s == nil) != (y.%s == nil) {" % (fname, fname),
                      "\t\treturn false",
                      "\t}",
                      "\tif x.%s != nil && !x.%s.EqualMessage(y.%s) {" % (fname, fname, fname),
                      "\t\treturn false",
                      "\t}"]
            elif kind == "rep-u64":
                mm += ["\tif len(src.%s) > 0 {" % fname,
                       "\t\tx.%s = append(x.%s, src.%s...)" % (fname, fname, fname),
                       "\t}"]
                e += ["\tif len(x.%s) != len(y.%s) {" % (fname, fname),
                      "\t\treturn false",
                      "\t}",
                      "\tfor i := 0; i < len(x.%s); i++ {" % fname,
                      "\t\tif x.%s[i] != y.%s[i] {" % (fname, fname),
                      "\t\t\treturn false",
                      "\t\t}",
                      "\t}"]
            elif kind == "rep-msg":
                mm += ["\tfor i := 0; i < len(src.%s); i++ {" % fname,
                       "\t\tel := &%s{}" % base,
                       "\t\tel.mergeMessage(src.%s[i])" % fname,
                       "\t\tx.%s = append(x.%s, el)" % (fname, fname),
                       "\t}"]
                e += ["\tif len(x.%s) != len(y.%s) {" % (fname, fname),
                      "\t\treturn false",
                      "\t}",
                      "\tfor i := 0; i < len(x.%s); i++ {" % fname,
                      "\t\tex := x.%s[i]" % fname,
                      "\t\tif ex == nil {",
                      "\t\t\tex = &%s{}" % base,
                      "\t\t}",
                      "\t\tey := y.%s[i]" % fname,
                      "\t\tif ey == nil {",
                      "\t\t\tey = &%s{}" % base,
                      "\t\t}",
                      "\t\tif !ex.EqualMessage(ey) {",
                      "\t\t\treturn false",
                      "\t\t}",
                      "\t}"]
            else:
                refuse("no clone/equal rule for field %s.%s of type %s"
                       % (name, fname, ftype))
        mm += ["\tif len(src.unknownFields) > 0 {",
               "\t\tx.unknownFields = append(x.unknownFields, src.unknownFields...)",
               "\t}",
               "}"]
        e += ["\treturn equalUnknown(x.unknownFields, y.unknownFields)", "}"]
        out.append("\n".join(mm))
        records.append(("method %s.mergeMessage" % recv,
                        "internal/impl/merge.go:36-113 mergePointer; merge_gen.go mergeUint64Ptr :122 / mergeBoolPtr :22 / mergeInt32Ptr :47 / mergeUint64Slice :130; merge.go mergeMessage :159 / mergeMessageSlice :175 / mergeBytes :187",
                        "writes *x (allocating cells, slices, embedded messages, unknownFields); reads *src (recursively)", "-"))
        out.append("\n".join(e))
        records.append(("method %s.EqualMessage" % recv,
                        "internal/impl/equal.go:22-132 equalMessage (+ :177-190 equalMessageList; the nil-element slow path reflect/protoreflect/value_equal.go equalMessage), :193-224 equalUnknown",
                        "allocates (equalUnknown's concatenations); reads *x, *y (recursively)", "-"))
    return "\n\n".join(out) + "\n"


# ---- the proto stand-in (proto/proto.go) ------------------------------------

# The protobuf-runtime functions the vendored tree calls.  `derive.py` emits a
# subject-local `proto` package declaring exactly these (plus the error
# machinery and the dispatch interface), and REFUSES if the tree reaches for
# one that is not here — so a raft rev that starts calling `proto.Merge`
# cannot slip through.  Route A (D2): Equal joins the set — upstream
# raftpb/confstate.go is vendored verbatim since S1 and calls it.
PROTO_FUNCS = {
    "Clone": "func Clone(m Message) Message",
    "Equal": "func Equal(x, y Message) bool",
    "Marshal": "func Marshal(m Message) ([]byte, error)",
    "Unmarshal": "func Unmarshal(b []byte, m Message) error",
    "Size": "func Size(m Message) int",
}
PROTO_PATH = "google.golang.org/protobuf/proto"

PROTO_HEADER = """// Code GENERATED by tools/raftsubject/derive.py. DO NOT EDIT — edit the
// derivation.
//
// The subject-local stand-in for %(path)s
// (%(pb)s), ROUTE A shape A1 (docs/2026-10-04_route-a-protobuf-design.md
// D2/D4/D5). The entry points keep upstream's signatures and their nil /
// typed-nil arms, then DISPATCH THROUGH AN INTERFACE to the generated
// per-type codec (raftpb/plain_codec.go) — this package does NOT import
// raftpb; raftpb imports it, as upstream's generated code imports
// protoimpl. A message type outside the plainpb nine fails the `methods`
// assertion and panics BY NAME — never a silent zero.
//
// The error machinery is internal/errors' (errors.go:16-42): ONE
// `*prefixError` type whose Error() is prefix + text and whose Unwrap()
// is the sentinel Error, so errors.Is(err, proto.Error) holds under
// `go run` (on the machine errors.Is is refused by name, FR-14/G6 — D10).
// The prefix's spacing is detrand's per-BINARY bit (internal/detrand/
// rand.go:25-27): LATITUDE, modeled as ONE labelled choice consumed at
// package init — rand.Intn(2) on the machine's general [0, n) pick site
// (ChoiceSite.intn; index 0 = U+0020, detrand's failure default; 1 =
// U+00A0) — ruled [USER] 2026-10-04 (Q1, relayed).

package proto

import (
	"errors"
	"math/rand"
)
"""

PROTO_COMMON = '''
// Error — proto/proto.go:32-35 (= internal/errors/errors.go:16): the
// sentinel every error this package produces unwraps to.
var Error = errors.New("protobuf error")

// prefixError — internal/errors/errors.go:24.
type prefixError struct{ s string }

// prefix — internal/errors/errors.go:26-34, computed ONCE at package init.
var prefix = pickPrefix()

// pickPrefix — the init-time spelling pick (D5, Q1): detrand.Bool()
// (internal/detrand/rand.go:25-27) is a function of the executable's bytes,
// so the weakest machine admits both members; ONE draw from the [0, 2) pick
// site. 0 = "proto: " (U+0020, detrand's failure default), 1 = "proto:"
// + U+00A0.
func pickPrefix() string {
	k := rand.Intn(2)
	if k == 1 {
		return "proto:\\u00a0"
	}
	return "proto: "
}

// Error — internal/errors/errors.go:36-38.
func (e *prefixError) Error() string {
	return prefix + e.s
}

// Unwrap — internal/errors/errors.go:40-42.
func (e *prefixError) Unwrap() error {
	return Error
}

// NewError — internal/errors/errors.go:20-22 New, without format verbs (the
// two values the codec needs carry fixed text). Exported only because the
// generated codec (raftpb, the internal/impl twin) declares errDecode and
// errRecursionDepth through it, as impl/decode.go:19-20 declare them
// through internal/errors; not part of upstream proto's API.
func NewError(s string) error {
	return &prefixError{s: s}
}

// Message is the interface the vendored callers pass (upstream's parameter
// type). Every plainpb message type satisfies it through its generated
// ProtoMessage() marker method, kept verbatim.
type Message interface {
	ProtoMessage()
}

// methods — the generated fast-path table (protoiface.Methods as
// protoMethods returns it): what every plainpb message type implements in
// raftpb/plain_codec.go.
type methods interface {
	IsNilMessage() bool
	ResetMessage()
	SizeMessage() int
	MarshalAppend(b []byte) []byte
	UnmarshalMessage(b []byte, depth int) error
	ProtoClone() Message
	ProtoEqual(y Message) bool
}

// emptyBuf — proto/decode_gen.go:603.
var emptyBuf [0]byte

// defaultRecursionLimit — encoding/protowire/wire.go:28.
const defaultRecursionLimit = 10000
'''

PROTO_BODIES = {
    "Clone": '''// Clone — proto/merge.go:41-60: nil -> nil; a typed nil -> the typed nil
// (Type().Zero().Interface()); else New + merge.
func Clone(m Message) Message {
	if m == nil {
		return nil
	}
	x, ok := m.(methods)
	if !ok {
		panic("proto: Clone on a message type outside the plainpb nine (fail closed; extend the derivation after reading the new type)")
	}
	if x.IsNilMessage() {
		return m
	}
	return x.ProtoClone()
}''',
    "Equal": '''// Equal — proto/equal.go:42-66: a nil interface equals only a nil
// interface; identical pointers are equal; validity must agree; then the
// generated fast path (impl/equal.go:22). Upstream's identical-pointer
// shortcut is guarded by reflect (Kind == Ptr); every plainpb message is
// a pointer, so the guard here is the methods assertion, taken first.
func Equal(x, y Message) bool {
	if x == nil || y == nil {
		return x == nil && y == nil
	}
	mx, ok := x.(methods)
	if !ok {
		panic("proto: Equal on a message type outside the plainpb nine (fail closed; extend the derivation after reading the new type)")
	}
	my, ok := y.(methods)
	if !ok {
		panic("proto: Equal on a message type outside the plainpb nine (fail closed; extend the derivation after reading the new type)")
	}
	if x == y {
		return true
	}
	if mx.IsNilMessage() != my.IsNilMessage() {
		return false
	}
	return mx.ProtoEqual(y)
}''',
    "Marshal": '''// Marshal — proto/encode.go:105-116: a nil interface -> nil, nil; an empty
// encoding -> emptyBytesForMessage (:141-146): nil for a TYPED-NIL
// message, the non-nil empty buffer for a valid one. The error is always
// nil on these schemas.
func Marshal(m Message) ([]byte, error) {
	if m == nil {
		return nil, nil
	}
	x, ok := m.(methods)
	if !ok {
		panic("proto: Marshal on a message type outside the plainpb nine (fail closed; extend the derivation after reading the new type)")
	}
	b := x.MarshalAppend(nil)
	if len(b) == 0 {
		if x.IsNilMessage() {
			return nil, nil
		}
		return emptyBuf[:], nil
	}
	return b, nil
}''',
    "Size": '''// Size — proto/size.go:19-35: nil -> 0; a typed nil -> 0 (sizePointer).
func Size(m Message) int {
	if m == nil {
		return 0
	}
	x, ok := m.(methods)
	if !ok {
		panic("proto: Size on a message type outside the plainpb nine (fail closed; extend the derivation after reading the new type)")
	}
	return x.SizeMessage()
}''',
    "Unmarshal": '''// Unmarshal — proto/decode.go:61-64 + :90-135 unmarshal: Reset (the
// generated Reset; a typed nil nil-dereferences there, as upstream's
// does), then the generated fast path with RecursionLimit 10000;
// checkInitialized never fails (no required field). A nil interface
// nil-dereferences at the method call, as upstream's m.ProtoReflect()
// does.
func Unmarshal(b []byte, m Message) error {
	if m == nil {
		m.ProtoMessage()
	}
	x, ok := m.(methods)
	if !ok {
		panic("proto: Unmarshal on a message type outside the plainpb nine (fail closed; extend the derivation after reading the new type)")
	}
	x.ResetMessage()
	return x.UnmarshalMessage(b, defaultRecursionLimit)
}''',
}

PROTO_TWINS = {
    "Clone": ("proto/merge.go:41-60 Clone", "allocates (the deep copy); reads the message"),
    "Equal": ("proto/equal.go:42-66 Equal", "pure: reads both messages"),
    "Marshal": ("proto/encode.go:105-116 Marshal, :141-146 emptyBytesForMessage", "allocates the encoding; reads the message"),
    "Unmarshal": ("proto/decode.go:61-64 Unmarshal, :90-135 unmarshal; proto/reset.go:16-22 Reset", "writes the message (reset, then decode); reads b"),
    "Size": ("proto/size.go:19-35 Size", "pure: reads the message"),
}


def gen_proto(used, records):
    """Emit the subject-local proto package: the error machinery, the
    dispatch interface, and exactly the used entry points."""
    unknown = sorted(u for u in used if u not in PROTO_FUNCS)
    if unknown:
        refuse("the vendored tree calls proto.%s, which the stand-in does not "
               "declare — read the new call site and extend PROTO_FUNCS "
               "(fail-closed by design)" % ", proto.".join(unknown))
    out = [PROTO_HEADER % {"path": PROTO_PATH, "pb": PB_VERSION} + PROTO_COMMON.rstrip("\n")]
    records += [
        ("var proto.Error", "proto/proto.go:32-35 (internal/errors/errors.go:16)", "package state, set once at init", "-"),
        ("type proto.prefixError", "internal/errors/errors.go:24", "-", "-"),
        ("var proto.prefix", "internal/errors/errors.go:26-34 (the per-binary detrand bit)", "package state, set once at init by ONE ChoiceSite.intn draw (bound 2)", "-"),
        ("func proto.pickPrefix", "internal/detrand/rand.go:25-27 Bool (+ errors.go:26-34)", "ONE choice: rand.Intn(2), consumed before main", "-"),
        ("method (*proto.prefixError).Error", "internal/errors/errors.go:36-38", "pure: reads prefix, e.s", "-"),
        ("method (*proto.prefixError).Unwrap", "internal/errors/errors.go:40-42", "pure", "-"),
        ("func proto.NewError", "internal/errors/errors.go:20-22 New (no format verbs)", "allocates the *prefixError", "-"),
        ("var proto.emptyBuf", "proto/decode_gen.go:603", "package state, zero-length", "-"),
    ]
    for name in sorted(used):
        body = PROTO_BODIES[name]
        if PROTO_FUNCS[name] not in body:
            refuse("internal: proto.%s body does not carry its pinned signature" % name)
        out.append(body)
        twin, fp = PROTO_TWINS[name]
        records.append(("func proto.%s" % name, twin, fp, "-"))
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


# ---- the corpus mirror (D9 / acceptance §5: the language shapes) -----------
#
# Corpus/coverage/exec/multipkg/wire-codec/ pins, differentially (go run vs
# the machine, stdlib only — protobuf-go is never a corpus oracle), the
# LANGUAGE SHAPES the generated codec runs on. Since route A S1 its two local
# packages are not hand-mirrored: they are THIS generator's output over a
# small synthetic schema (four messages: a self-recursive one with every
# field kind, so the recursion edges, groups, unknowns and typed nils are
# all reachable), renamed raftpb -> wirepb and proto -> wireproto. --check
# regenerates them and fails on drift, so a generator change (the Q5
# dispatch-form flip included) moves the corpus pin in the same commit.
MIRROR_DIR = "Corpus/coverage/exec/multipkg/wire-codec"
MIRROR_ENUMS = ["EntryType", "ConfChangeType"]
MIRROR_SCHEMA = [
    ("Entry", [
        ("Term", "*uint64", '`protobuf:"varint,2,opt,name=Term"`'),
        ("Index", "*uint64", '`protobuf:"varint,3,opt,name=Index"`'),
        ("Type", "*EntryType", '`protobuf:"varint,1,opt,name=Type,enum=wirepb.EntryType"`'),
        ("Data", "[]byte", '`protobuf:"bytes,4,opt,name=Data"`'),
    ]),
    ("ConfChange", [
        ("Type", "*ConfChangeType", '`protobuf:"varint,2,opt,name=type,enum=wirepb.ConfChangeType"`'),
        ("NodeId", "*uint64", '`protobuf:"varint,3,opt,name=node_id"`'),
        ("Context", "[]byte", '`protobuf:"bytes,4,opt,name=context"`'),
        ("Id", "*uint64", '`protobuf:"varint,1,opt,name=id"`'),
    ]),
    ("ConfState", [
        ("Voters", "[]uint64", '`protobuf:"varint,1,rep,name=voters"`'),
        ("AutoLeave", "*bool", '`protobuf:"varint,5,opt,name=auto_leave"`'),
    ]),
    ("Message", [
        ("To", "*uint64", '`protobuf:"varint,2,opt,name=to"`'),
        ("Entries", "[]*Entry", '`protobuf:"bytes,7,rep,name=entries"`'),
        ("Conf", "*ConfState", '`protobuf:"bytes,9,opt,name=conf"`'),
        ("Context", "[]byte", '`protobuf:"bytes,12,opt,name=context"`'),
        ("Responses", "[]*Message", '`protobuf:"bytes,14,rep,name=responses"`'),
    ]),
]

MIRROR_HEADER = """// Code GENERATED by tools/raftsubject/derive.py (the corpus mirror, route A
// S1). DO NOT EDIT — derive.py --check regenerates and compares it.
//
// The route A codec generator's output over a four-message SYNTHETIC schema
// (MIRROR_SCHEMA), renamed raftpb -> wirepb and proto -> wireproto: the
// corpus pin for the language shapes raftsubject's generated codec runs on.
"""


def mirror_rename(text):
    text = text.replace("\npackage raftpb\n", "\npackage wirepb\n")
    text = text.replace("\npackage proto\n", "\npackage wireproto\n")
    text = text.replace('\t"proto"\n', '\t"wireproto"\n')
    text = text.replace('import "proto"\n', 'import "wireproto"\n')
    text = re.sub(r"\bproto\.(NewError|Message)\b", r"wireproto.\1", text)
    return MIRROR_HEADER + "\n" + text


def gen_corpus_mirror(out_dir):
    """Write wirepb/ and wireproto/ under out_dir (the case directory)."""
    msgs = {}
    for name, fields in MIRROR_SCHEMA:
        m = Msg(name)
        m.fields = list(fields)
        m.has_unknown = True
        msgs[name] = m
    enums = set(MIRROR_ENUMS)
    types = ["package wirepb", ""]
    for e in MIRROR_ENUMS:
        types += ["type %s int32" % e, ""]
    for name, fields in MIRROR_SCHEMA:
        types.append("type %s struct {" % name)
        for fname, ftype, ftag in fields:
            types.append("\t%s %s %s" % (fname, ftype, ftag))
        types += ["\tunknownFields []byte", "}", "",
                  "func (*%s) ProtoMessage() {}" % name, ""]
    files = {
        "wirepb/types.go": MIRROR_HEADER + "\n" + "\n".join(types),
        "wirepb/plain_wire.go": mirror_rename(gen_wire()),
        "wirepb/plain_codec.go": mirror_rename(gen_codec(msgs, enums, [])),
        "wirepb/plain_clone.go": mirror_rename(gen_clone(msgs, enums, [])),
        "wireproto/proto.go": mirror_rename(gen_proto(set(PROTO_FUNCS), [])),
    }
    for rel, text in sorted(files.items()):
        if re.search(r"\braftpb\b\.|\bproto\.(NewError|Message)\b", re.sub(r"//.*", "", text)):
            refuse("corpus mirror %s still names raftpb./proto. in code" % rel)
        dst = os.path.join(out_dir, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with open(dst, "w") as f:
            f.write(text)
    gofmt = subprocess.run(["gofmt", "-w", os.path.join(out_dir, "wirepb"),
                            os.path.join(out_dir, "wireproto")], capture_output=True, text=True)
    if gofmt.returncode != 0:
        refuse("gofmt failed on the corpus mirror:\n%s" % gofmt.stderr)
    return sorted(files)


GENERATED_FILES = ["raftpb/plain_wire.go", "raftpb/plain_codec.go",
                   "raftpb/plain_clone.go", "proto/proto.go"]


def generated_digests(out_dir):
    return {g: digest(os.path.join(out_dir, g)) for g in GENERATED_FILES}


def render_funcids(funcids, out_dir):
    """D8 (the logic team's (a), (b), (e)): every generated function,
    method and package-level value of the route A codec, with its upstream
    twin and its footprint; the dispatch column names the Q5 sites. The
    trailer pins the generated files' digests (also in GENERATED_DIGESTS)."""
    keys = [r[0] for r in funcids]
    if len(set(keys)) != len(keys):
        refuse("duplicate FuncId rows: %s" % sorted(k for k in keys if keys.count(k) > 1))
    lines = [
        "# codec-funcids.tsv — GENERATED by tools/raftsubject/derive.py (route A D8,",
        "# docs/2026-10-04_route-a-protobuf-design.md). DO NOT EDIT; --check compares it.",
        "# Upstream twins: %s, paths relative to google.golang.org/protobuf@v1.36.11." % PB_VERSION,
        "# dispatch: the field-number dispatch form of the row's body (Q5 PENDING —",
        "# DISPATCH_FORM in derive.py; '-' = no field-number dispatch).",
        "# wire_key\tfile\tupstream_twin\tfootprint\tdispatch"]
    for r in funcids:
        lines.append("\t".join(r))
    dg = generated_digests(out_dir)
    for g in GENERATED_FILES:
        lines.append("# sha256 %s %s" % (dg[g], g))
    return "\n".join(lines) + "\n"


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
    funcids = []  # D8: (wire key, file, upstream twin, footprint, dispatch)
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
            for fp in WIRE_FUNCS:
                funcids.append((fp[0], "raftpb/plain_wire.go", fp[1], fp[2], "-"))
            with open(os.path.join(out_dir, "raftpb", "plain_wire.go"), "w") as f:
                f.write(gen_wire())
            recs = []
            with open(os.path.join(out_dir, "raftpb", "plain_codec.go"), "w") as f:
                f.write(gen_codec(msgs, enums, recs))
            funcids += [(r[0], "raftpb/plain_codec.go", r[1], r[2], r[3]) for r in recs]
            recs = []
            with open(os.path.join(out_dir, "raftpb", "plain_clone.go"), "w") as f:
                f.write(gen_clone(msgs, enums, recs))
            funcids += [(r[0], "raftpb/plain_clone.go", r[1], r[2], r[3]) for r in recs]
            report.append("plainpb  %-32s (%d msgs, %d enums, %d stubs, %d drops)"
                          % (outp, len(msgs), len(enums), len(stubbed), len(dropped)))
            report.append("generate %-32s (protowire/impl twins, %d entries)"
                          % ("raftpb/plain_wire.go", len(WIRE_FUNCS)))
            report.append("generate %-32s (IsNil/Reset/Size/MarshalAppend/Unmarshal/ProtoClone/ProtoEqual x %d; dispatch form %s)"
                          % ("raftpb/plain_codec.go", len(msgs), DISPATCH_FORM))
            report.append("generate %-32s (CloneMessage/mergeMessage/EqualMessage x %d)"
                          % ("raftpb/plain_clone.go", len(msgs)))
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
            recs = []
            f.write(gen_proto(proto_used, recs))
            funcids += [(r[0], "proto/proto.go", r[1], r[2], r[3]) for r in recs]
        report.append("generate %-32s (%d codec dispatch function%s: %s)"
                      % ("proto/proto.go", len(proto_used),
                         "" if len(proto_used) == 1 else "s",
                         ", ".join(sorted(proto_used))))

    gofmt = subprocess.run(["gofmt", "-w", out_dir], capture_output=True, text=True)
    if gofmt.returncode != 0:
        refuse("gofmt failed on the derived tree:\n%s" % gofmt.stderr)

    # D8: the FuncId table (wire key, file, twin, footprint, dispatch form)
    # and the digests of the generated files, written beside the tree as
    # `.funcids.tsv` (main() places it at FUNCIDS_PATH / compares it).
    if plainpb_msgs is None:
        refuse("no plainpb step ran — the codec FuncId table cannot be built")
    with open(os.path.join(out_dir, ".funcids.tsv"), "w") as f:
        f.write(render_funcids(funcids, out_dir))

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
    ap.add_argument("--print-generated-digests", action="store_true",
                    help="derive to a temp dir and print the GENERATED_DIGESTS "
                         "table to paste (D8; a human act, like --print-digests)")
    args = ap.parse_args()
    funcids_out = os.path.join(REPO, FUNCIDS_PATH)

    def digest_mismatch(tree):
        got = generated_digests(tree)
        return [g for g in GENERATED_FILES if GENERATED_DIGESTS.get(g) != got[g]], got

    if args.print_generated_digests:
        tmp = tempfile.mkdtemp(prefix="raftsubject-gen-")
        try:
            derive(args.raft, tmp, verbose=False)
            _bad, got = digest_mismatch(tmp)
            print("GENERATED_DIGESTS = {")
            for g in GENERATED_FILES:
                print('    "%s": "%s",' % (g, got[g]))
            print("}")
        finally:
            shutil.rmtree(tmp)
        return

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
            bad, _got = digest_mismatch(tmp)
            for g in bad:
                drift.append("%s (generated digest differs from GENERATED_DIGESTS — "
                             "the generator's output moved; review, then paste "
                             "--print-generated-digests)" % g)
            fresh_ids = os.path.join(tmp, ".funcids.tsv")
            if not os.path.exists(funcids_out) or \
                    not filecmp.cmp(fresh_ids, funcids_out, shallow=False):
                drift.append(FUNCIDS_PATH + " (FuncId table differs from the derivation)")
            os.remove(fresh_ids)
            mtmp = os.path.join(tmp, ".mirror")
            for rel in gen_corpus_mirror(mtmp):
                tracked = os.path.join(REPO, MIRROR_DIR, rel)
                if not os.path.exists(tracked) or \
                        not filecmp.cmp(os.path.join(mtmp, rel), tracked, shallow=False):
                    drift.append("%s/%s (corpus mirror differs from the generator)" % (MIRROR_DIR, rel))
            for sub in ("wirepb", "wireproto"):
                d = os.path.join(REPO, MIRROR_DIR, sub)
                for fn in (sorted(os.listdir(d)) if os.path.isdir(d) else []):
                    if fn.endswith(".go") and not os.path.exists(os.path.join(mtmp, sub, fn)):
                        drift.append("%s/%s/%s (tracked in the mirror but not generated)" % (MIRROR_DIR, sub, fn))
            shutil.rmtree(mtmp)
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
    shutil.move(os.path.join(args.out, ".funcids.tsv"), funcids_out)
    mirror_dir = os.path.join(REPO, MIRROR_DIR)
    stale = os.path.join(mirror_dir, "wirepb", "wirepb.go")
    if os.path.exists(stale):
        os.remove(stale)  # the pre-route-A hand mirror, superseded
    gen_corpus_mirror(mirror_dir)
    bad, _got = digest_mismatch(args.out)
    if bad:
        refuse("the tree was written, but the generated file(s) %s differ from "
               "GENERATED_DIGESTS — review the generator change, then paste the "
               "table printed by --print-generated-digests (fail closed: an "
               "unreviewed generator move is not a derivation)" % ", ".join(bad))


if __name__ == "__main__":
    main()
