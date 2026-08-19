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
            protobuf runtime, or — for logger.go — is the W2.2 no-op Logger
            injection).  The upstream file's SHA-256 is PINNED here: when the
            pin moves and upstream changes, the derivation FAILS LOUD and the
            overlay must be revisited by hand.  That digest pin is the
            re-derivation contract for the files a script cannot derive.

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
    ("logger.go", "raft/logger.go", "overlay"),
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
}

# Packages that exist in the subject tree, hence whose import paths get
# rewritten from the module path to the short dot-free form.
SUBJECT_PACKAGES = ["quorum", "raftpb", "tracker"]

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
// MARSHAL-AVOIDANCE: no Marshal/Unmarshal/Size lives here at all. The
// harness passes structs (no wire encode), MemoryStorage stores structs,
// and membership is snapshot-seeded, so the encode paths are provably never
// taken. Anything that reaches for them hits an explicit panic, never a
// silent zero."""


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
    return src, n


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
    for up, outp, mode in VENDOR:
        src = open(os.path.join(raft_dir, up)).read()
        dst = os.path.join(out_dir, outp)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        if mode == "verbatim":
            text, n = rewrite_imports(src)
            report.append("verbatim %-32s (%d import path%s rewritten)"
                          % (outp, n, "" if n == 1 else "s"))
        elif mode == "plainpb":
            text, msgs, enums, stubbed, dropped = plainpb(src)
            with open(os.path.join(out_dir, "raftpb", "plain_clone.go"), "w") as f:
                f.write(gen_clone(msgs, enums))
            report.append("plainpb  %-32s (%d msgs, %d enums, %d stubs, %d drops)"
                          % (outp, len(msgs), len(enums), len(stubbed), len(dropped)))
            report.append("generate %-32s (CloneMessage/EqualMessage x %d)"
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
        with open(dst, "w") as f:
            f.write(text)

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
