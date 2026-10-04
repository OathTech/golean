"""difftest_sec8.py — difftest.py SECTION 8: the route A exactness battery.

ROUTE A (docs/2026-10-04_route-a-protobuf-design.md D9, acceptance §5; ratified
[USER] Mike 2026-10-04 «Approved», relayed). Section 7 probes WELL-FORMED
values, so it is blind to the three recorded deltas U-1/U-2/U-3. Section 8
drives the subject's `proto` package and protobuf-go v1.36.11 over the SAME
bytes and constructed values, and requires, per input:

  * the verdict (nil vs non-nil error);
  * errors.Is(err, proto.Error) on both sides;
  * the error TEXT, equal after normalizing the ONE prefix byte (the
    reference binary's bit is recorded; the subject's spelling must be one
    of the two members);
  * proto.Size and proto.Marshal BYTES (nil-ness included) of the message
    AFTER the call — on success and on error alike (the partial state of a
    failed decode is observable to a client);
  * proto.Clone (re-marshalled bytes) and proto.Equal(Clone(x), x);
  * proto.Equal over every ordered pair of decoded values of one type.

EXACT = all of these. There is NO note class in section 8: any difference
is a DISAGREE and fails the run.

Inputs: the 26-entry corpus imported VERBATIM from raft-proofs
`fixtures/i6/malformed-conf-bytes.json` @ f3d857f (frozen; sha256 pinned
below, fail closed on drift) — plus a GENERATED adversarial battery over all
nine message types as top-level subjects (every known field valid and at
every wrong wire type, unknown fields of every wire type at every position,
non-minimal tags, groups nested 0-3 and malformed, field-number edges incl.
the top-level-vs-in-group asymmetry, 10-byte varints and overflow, packed
repeated fields, unlisted enum values, merge-twice singular messages,
reordered unknowns for Equal, nil/empty), the recursion edges (10000 vs
10001 nested Message.responses; 10001 vs 10002 nested unknown groups), and
constructed values (typed nils of every type; nil elements of repeated
message fields).

The generator is deterministic; the inputs are a function of the schema
derive.py parses out of raft.pb.go.
"""

import hashlib
import json
import os

FIXTURE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fixtures",
                       "i6-malformed-conf-bytes.json")
# raft-proofs f3d857f36c9085003e4788b512709cdb7dc8f754, fixtures/i6/
# malformed-conf-bytes.json, copied byte-for-byte (`git show
# f3d857f:fixtures/i6/malformed-conf-bytes.json`), 2026-10-04.
FIXTURE_SHA256 = "cd724c9b40a96879c024ffe5b0c8f494c44ff2fe87a59484c15f6d19ebca5dd9"
FIXTURE_ENTRIES = 26


def load_corpus(refuse):
    raw = open(FIXTURE, "rb").read()
    got = hashlib.sha256(raw).hexdigest()
    if got != FIXTURE_SHA256:
        refuse("section 8: the imported corpus %s changed (%s != pinned %s) — it "
               "is FROZEN; extend only with a new dated list" % (FIXTURE, got[:12], FIXTURE_SHA256[:12]))
    d = json.loads(raw)
    if d.get("schema") != "i6-malformed-conf-bytes-v1" or len(d["entries"]) != FIXTURE_ENTRIES:
        refuse("section 8: unexpected corpus shape (schema %r, %d entries)"
               % (d.get("schema"), len(d.get("entries", []))))
    out = []
    for e in d["entries"]:
        typ = {"v1": "ConfChange", "v2": "ConfChangeV2"}.get(e["kind"])
        if typ is None:
            refuse("section 8: corpus entry %s has unknown kind %r" % (e["name"], e["kind"]))
        out.append(("corpus/" + e["name"], typ, e["data"]))  # None = nil data
    return out


# ---- wire encoders -----------------------------------------------------------

def varint(v):
    out = bytearray()
    while v >= 0x80:
        out.append((v & 0x7F) | 0x80)
        v >>= 7
    out.append(v)
    return bytes(out)


def tag(num, wt):
    return varint(num << 3 | wt)


def f_varint(num, v):
    return tag(num, 0) + varint(v)


def f_bytes(num, payload):
    return tag(num, 2) + varint(len(payload)) + payload


def f_fixed32(num):
    return tag(num, 5) + b"\x01\x02\x03\x04"


def f_fixed64(num):
    return tag(num, 1) + b"\x01\x02\x03\x04\x05\x06\x07\x08"


def f_group(num, inner):
    return tag(num, 3) + inner + tag(num, 4)


U64MAX = (1 << 64) - 1


def unknowns(num):
    """One unknown field of every wire type at field number num."""
    return [
        ("varint", f_varint(num, 42)),
        ("fixed64", f_fixed64(num)),
        ("bytes", f_bytes(num, b"\xff\x00")),
        ("fixed32", f_fixed32(num)),
        ("group-empty", f_group(num, b"")),
        ("group-d1", f_group(num, f_varint(1, 5) + f_bytes(2, b"z"))),
        ("group-d3", f_group(num, f_group(num + 1, f_group(num + 2, f_fixed32(9) + f_varint(3, 1))))),
    ]


def battery(msgs, enums, message_fields):
    """-> [(name, type, hex)] — the generated adversarial inputs."""
    out = []

    def add(t, name, b):
        out.append(("gen/%s/%s" % (t, name), t, b.hex()))

    for t in msgs:
        fields = message_fields(msgs, enums, t)
        known = {num for num, _f, _ty, _k in fields}
        unk = 15
        while unk in known:
            unk += 1
        add(t, "nil", b"")  # replaced by a nil slice below (name-keyed)
        add(t, "empty", b"")
        # every known field: valid values, then every WRONG wire type.
        valid = []
        for num, fname, ftype, kind in fields:
            base = ftype.lstrip("*[]")
            vals = []
            if kind == "scalar-u64":
                vals = [("0", f_varint(num, 0)), ("300", f_varint(num, 300)),
                        ("max", f_varint(num, U64MAX))]
            elif kind == "scalar-bool":
                vals = [("false", f_varint(num, 0)), ("true", f_varint(num, 1)),
                        ("two", f_varint(num, 2))]
            elif kind == "scalar-enum":
                vals = [("0", f_varint(num, 0)), ("1", f_varint(num, 1)),
                        ("unlisted-99", f_varint(num, 99)),
                        ("neg1", f_varint(num, U64MAX)),
                        ("int32-trunc", f_varint(num, (1 << 32) + 5))]
            elif kind == "bytes":
                vals = [("empty", f_bytes(num, b"")), ("ab", f_bytes(num, b"ab"))]
            elif kind == "msg":
                inner_fields = message_fields(msgs, enums, base)
                fnum = inner_fields[0][0]
                ikind = inner_fields[0][3]
                inner = f_varint(fnum, 7) if ikind in ("scalar-u64", "scalar-bool", "scalar-enum", "rep-u64") \
                    else f_bytes(fnum, b"")
                vals = [("empty", f_bytes(num, b"")),
                        ("nested", f_bytes(num, inner)),
                        ("nested-unknown", f_bytes(num, inner + f_varint(15 if 15 not in {f[0] for f in inner_fields} else 16, 1))),
                        ("merge-twice", f_bytes(num, inner) + f_bytes(num, f_varint(15, 2)))]
            elif kind == "rep-u64":
                vals = [("two", f_varint(num, 1) + f_varint(num, 2)),
                        ("packed", f_bytes(num, varint(1) + varint(300) + varint(U64MAX))),
                        ("packed-empty", f_bytes(num, b"")),
                        ("packed-then-unpacked", f_bytes(num, varint(4)) + f_varint(num, 5)),
                        ("packed-truncated-elem", f_bytes(num, b"\x80")),
                        ("packed-overflow-elem", f_bytes(num, b"\xff" * 9 + b"\x02"))]
            elif kind == "rep-msg":
                inner_fields = message_fields(msgs, enums, base)
                fnum = inner_fields[0][0]
                vals = [("one-empty", f_bytes(num, b"")),
                        ("two", f_bytes(num, f_varint(fnum, 3)) + f_bytes(num, b"")),
                        ("elem-unknown", f_bytes(num, f_varint(fnum, 3) + f_varint(15 if 15 not in {f[0] for f in inner_fields} else 16, 9))),
                        ("elem-malformed", f_bytes(num, b"\x08"))]
            for vn, b in vals:
                add(t, "%s-%s" % (fname, vn), b)
                valid.append(b)
            wts = {"scalar-u64": 0, "scalar-bool": 0, "scalar-enum": 0, "rep-u64": 0,
                   "bytes": 2, "msg": 2, "rep-msg": 2}[kind]
            for wt, body in ((0, varint(1)), (1, b"\x00" * 8), (2, varint(1) + b"q"),
                             (5, b"\x00" * 4), (3, tag(num, 4))):
                if wt == wts or (kind == "rep-u64" and wt == 2):
                    continue
                add(t, "%s-wiretype%d" % (fname, wt), tag(num, wt) + body)
            # a known field's value truncated
            add(t, "%s-truncated" % fname, tag(num, wts) + (b"\x80" if wts == 0 else b"\x05ab"))
        allvalid = b"".join(v for v in valid if v)
        # unknown fields of every wire type, at every position.
        for un, ub in unknowns(unk):
            add(t, "unknown-%s-alone" % un, ub)
            if valid:
                add(t, "unknown-%s-before" % un, ub + valid[0])
                add(t, "unknown-%s-after" % un, valid[0] + ub)
                add(t, "unknown-%s-between" % un, valid[0] + ub + valid[-1])
        add(t, "unknown-two-byte-tag", f_varint(16 if 16 not in known else 17, 1))
        add(t, "unknown-number-max", f_varint((1 << 29) - 1, 1))
        add(t, "unknown-noncanonical-tag", b"\xf8\x80\x00\x01")  # field 15 varint, 3-byte tag
        if fields:
            num0, kind0 = fields[0][0], fields[0][3]
            wt0 = 2 if kind0 in ("bytes", "msg", "rep-msg") else 0
            t0 = num0 << 3 | wt0  # < 0x80: every schema's first field is <= 15
            add(t, "known-noncanonical-tag", bytes([t0 | 0x80, 0x00]) + (b"\x00" if wt0 == 2 else b"\x01"))
        # reordered unknowns: across numbers (Equal) and within one number (not).
        add(t, "unknown-order-ab", f_varint(unk, 1) + f_varint(unk + 1, 2))
        add(t, "unknown-order-ba", f_varint(unk + 1, 2) + f_varint(unk, 1))
        add(t, "unknown-same-num-xy", f_varint(unk, 1) + f_varint(unk, 2))
        add(t, "unknown-same-num-yx", f_varint(unk, 2) + f_varint(unk, 1))
        add(t, "unknown-interleaved-1", f_varint(unk, 1) + f_varint(unk + 1, 9) + f_varint(unk, 2))
        add(t, "unknown-interleaved-2", f_varint(unk + 1, 9) + f_varint(unk, 1) + f_varint(unk, 2))
        if allvalid:
            add(t, "all-valid", allvalid)
            add(t, "all-valid-reversed", b"".join(v for v in reversed(valid) if v))
        # malformations
        add(t, "tag-truncated", b"\x80")
        add(t, "tag-overflow-11", b"\xff" * 10 + b"\x01")
        add(t, "tag-ten-bytes", b"\xf8\xff\xff\xff\xff\xff\xff\xff\xff\x01" + b"\x00")
        add(t, "field-number-zero", b"\x00\x01")
        add(t, "field-number-zero-wt2", b"\x02\x00")
        add(t, "field-number-2^29-top", f_varint(1 << 29, 1))
        add(t, "field-number-2^29-in-group", f_group(unk, f_varint(1 << 29, 1)))
        add(t, "field-number-maxint32-in-group", f_group(unk, f_varint((1 << 31) - 1, 1)))
        add(t, "field-number-over-maxint32-in-group", f_group(unk, tag(1 << 31, 0) + b"\x01"))
        add(t, "field-number-zero-in-group", f_group(unk, b"\x00\x01"))
        add(t, "stray-end-group", tag(unk, 4))
        add(t, "stray-end-group-known", tag(fields[0][0], 4) if fields else tag(1, 4))
        add(t, "wire-type-6", tag(unk, 6) + b"\x00")
        add(t, "wire-type-7", tag(unk, 7))
        add(t, "wire-type-6-in-group", f_group(unk, tag(unk, 6)))
        add(t, "group-truncated", tag(unk, 3))
        add(t, "group-truncated-inner", tag(unk, 3) + f_varint(1, 1))
        add(t, "group-end-mismatch", tag(unk, 3) + tag(unk + 1, 4))
        add(t, "group-nested-end-mismatch", tag(unk, 3) + tag(unk + 1, 3) + tag(unk, 4) + tag(unk, 4))
        add(t, "group-inner-truncated-value", tag(unk, 3) + tag(1, 2) + b"\x05ab")
        add(t, "group-stray-end-inside", f_group(unk, tag(unk + 1, 4)))
        add(t, "varint-value-overflow", tag(unk, 0) + b"\xff" * 9 + b"\x02")
        add(t, "varint-value-ten-bytes", tag(unk, 0) + b"\xff" * 9 + b"\x01")
        add(t, "varint-value-truncated", tag(unk, 0) + b"\xff\xff")
        add(t, "fixed64-truncated", tag(unk, 1) + b"\x01\x02\x03")
        add(t, "fixed32-truncated", tag(unk, 5) + b"\x01")
        add(t, "bytes-length-overflow", tag(unk, 2) + b"\xff\xff\xff\xff\x0f")
        add(t, "bytes-length-huge-varint", tag(unk, 2) + b"\xff" * 9 + b"\x01")
        add(t, "bytes-truncated", tag(unk, 2) + b"\x05ab")
        if valid:
            add(t, "valid-then-malformed", valid[0] + b"\x80")
            add(t, "valid-unknown-then-malformed", valid[0] + f_varint(unk, 1) + tag(unk, 7))
    # the 'nil' rows decode nil data, not empty
    return [(n, t, None if n.endswith("/nil") else h) for n, t, h in out]


GO_SEC8 = r'''// Section 8 of the plainpb differential battery — GENERATED by
// tools/raftsubject/difftest_sec8.py. See that file for the contract.
package main

import (
	"bytes"
	"encoding/hex"
	"errors"
	"fmt"
	"os"
	"strings"

	"google.golang.org/protobuf/proto"

	up "go.etcd.io/raft/v3/raftpb"

	pp "golean.local/plainpbdiff/plainpb"
	pproto "golean.local/plainpbdiff/plainproto"
)

var _ = pp.EntryNormal

type sec8Type struct {
	name  string
	newUp func() proto.Message
	newPp func() pproto.Message
}

type sec8Input struct {
	name string
	typ  string
	hex  string
	nil_ bool
}

var sec8Checks int
var emitRef = os.Getenv("DIFFTEST_EMIT_REFERENCE") == "1"
var sec8RefBit = -1 // the reference binary's prefix bit (0 = U+0020, 1 = U+00A0)
var sec8SubjBit = -1

const nbsp = "proto:\u00a0"

func prefixBit(s string) int {
	if strings.HasPrefix(s, nbsp) {
		return 1
	}
	if strings.HasPrefix(s, "proto: ") {
		return 0
	}
	return -1
}

func normPrefix(s string) string {
	if strings.HasPrefix(s, nbsp) {
		return "proto: " + s[len(nbsp):]
	}
	return s
}

func errText(e error) string {
	if e == nil {
		return "<nil>"
	}
	return e.Error()
}

func hexOrNil(b []byte) string {
	if b == nil {
		return "nil"
	}
	return "[" + hex.EncodeToString(b) + "]"
}

%(EQUAL_SHIM)s

%(ERROR_SHIM)s

func sec8Compare(t sec8Type, name string, um proto.Message, uerr error, pm pproto.Message, perr error) {
	sec8Checks++
	if (uerr == nil) != (perr == nil) {
		report("S8/verdict/"+t.name, name, errText(uerr), errText(perr))
	}
	if uerr != nil && perr != nil {
		ub := prefixBit(uerr.Error())
		pb := prefixBit(perr.Error())
		if ub < 0 {
			report("S8/ref-prefix/"+t.name, name, uerr.Error(), "reference text carries neither prefix member")
		} else {
			if sec8RefBit >= 0 && sec8RefBit != ub {
				report("S8/ref-prefix-unstable/"+t.name, name, sec8RefBit, ub)
			}
			sec8RefBit = ub
		}
		if pb < 0 {
			report("S8/prefix-member/"+t.name, name, "proto: | proto:\\u00a0", perr.Error())
		} else {
			if sec8SubjBit >= 0 && sec8SubjBit != pb {
				report("S8/subject-prefix-unstable/"+t.name, name, sec8SubjBit, pb)
			}
			sec8SubjBit = pb
		}
		if normPrefix(uerr.Error()) != normPrefix(perr.Error()) {
			report("S8/text/"+t.name, name, uerr.Error(), perr.Error())
		}
		ui := errors.Is(uerr, proto.Error)
		pi := subjectIsError(perr)
		if ui != pi {
			report("S8/errors.Is/"+t.name, name, ui, pi)
		}
	}
	// The state after the call, success or error.
	if us, ps := proto.Size(um), pproto.Size(pm); us != ps {
		report("S8/size/"+t.name, name, us, ps)
	}
	ub, uerr2 := proto.Marshal(um)
	pb, perr2 := pproto.Marshal(pm)
	if uerr2 != nil || perr2 != nil {
		report("S8/marshal-err/"+t.name, name, errText(uerr2), errText(perr2))
	}
	if !bytes.Equal(ub, pb) || (ub == nil) != (pb == nil) {
		report("S8/marshal/"+t.name, name, hexOrNil(ub), hexOrNil(pb))
	}
	uc := proto.Clone(um)
	pc := pproto.Clone(pm)
	ucb, _ := proto.Marshal(uc)
	pcb, _ := pproto.Marshal(pc)
	if !bytes.Equal(ucb, pcb) || (ucb == nil) != (pcb == nil) {
		report("S8/clone-marshal/"+t.name, name, hexOrNil(ucb), hexOrNil(pcb))
	}
	ue := proto.Equal(uc, um)
	pe, ok := subjectEqual(pc, pm)
	if !ok || ue != pe {
		report("S8/clone-equal/"+t.name, name, ue, pe)
	}
}

func sec8Typed(t sec8Type, name string, u proto.Message, p pproto.Message) {
	// constructed values: Size, Marshal, Clone, Equal(x, x), Equal(x, zero)
	sec8Compare(t, name, u, nil, p, nil)
	ue := proto.Equal(u, t.newUp())
	pe, ok := subjectEqual(p, t.newPp())
	if !ok || ue != pe {
		report("S8/equal-vs-empty/"+t.name, name, ue, pe)
	}
	ue = proto.Equal(nil, u)
	pe, ok = subjectEqual(nil, p)
	if !ok || ue != pe {
		report("S8/equal-vs-nil-interface/"+t.name, name, ue, pe)
	}
	uc := proto.Clone(u)
	pc := pproto.Clone(p)
	if (uc == nil) != (pc == nil) {
		report("S8/clone-nil-interface/"+t.name, name, uc == nil, pc == nil)
	}
}

func section8() {
	types := map[string]sec8Type{
%(TYPES)s
	}
	inputs := []sec8Input{
%(INPUTS)s
	}
	decoded := map[string][][2]any{}
	order := []string{}
	for _, in := range inputs {
		t, ok := types[in.typ]
		if !ok {
			report("S8/type", in.name, in.typ, "unknown type")
			continue
		}
		var b []byte
		if !in.nil_ {
			var err error
			b, err = hex.DecodeString(in.hex)
			if err != nil {
				report("S8/hex", in.name, in.hex, err)
				continue
			}
			if b == nil {
				b = []byte{}
			}
		}
		um := t.newUp()
		uerr := proto.Unmarshal(b, um)
		pm := t.newPp()
		perr := pproto.Unmarshal(b, pm)
		sec8Compare(t, in.name, um, uerr, pm, perr)
		if emitRef && strings.HasPrefix(in.name, "corpus/") {
			// The REFERENCE (protobuf-go) outcome of an imported corpus entry,
			// for codeccheck.py's expectation table (--emit-reference).
			rb, _ := proto.Marshal(um)
			verdict, text := "ok", ""
			if uerr != nil {
				verdict, text = "err", normPrefix(uerr.Error())[len("proto: "):]
			}
			fmt.Printf("REF8\t%%s\t%%s\t%%s\t%%s\t%%d\t%%s\n", in.name, in.typ, verdict, text, proto.Size(um), hex.EncodeToString(rb))
		}
		if _, seen := decoded[in.typ]; !seen {
			order = append(order, in.typ)
		}
		decoded[in.typ] = append(decoded[in.typ], [2]any{um, pm})
	}
	// The recursion edges (D4): nested Message.responses and nested groups.
	nest := func(d int, wrap func([]byte) []byte) []byte {
		b := []byte{}
		for i := 0; i < d; i++ {
			b = wrap(b)
		}
		return b
	}
	resp := func(inner []byte) []byte {
		var l []byte
		n := uint64(len(inner))
		for n >= 0x80 {
			l = append(l, byte(n)|0x80)
			n >>= 7
		}
		l = append(l, byte(n))
		return append(append([]byte{0x72}, l...), inner...) // field 14, wire type 2
	}
	grp := func(inner []byte) []byte {
		return append(append([]byte{0x7b}, inner...), 0x7c) // field 15 group
	}
	mt := types["Message"]
	for _, d := range []int{9999, 10000} { // + the top-level message = 10000 / 10001 levels
		b := nest(d, resp)
		um := mt.newUp()
		uerr := proto.Unmarshal(b, um)
		pm := mt.newPp()
		perr := pproto.Unmarshal(b, pm)
		sec8Compare(mt, fmt.Sprintf("depth/responses-levels-%%d", d+1), um, uerr, pm, perr)
	}
	for _, d := range []int{10001, 10002} {
		b := nest(d, grp)
		um := mt.newUp()
		uerr := proto.Unmarshal(b, um)
		pm := mt.newPp()
		perr := pproto.Unmarshal(b, pm)
		sec8Compare(mt, fmt.Sprintf("depth/groups-%%d", d), um, uerr, pm, perr)
	}
	// Pairwise Equal over every decoded value of one type.
	pairs := 0
	for _, tn := range order {
		vs := decoded[tn]
		for i := range vs {
			for j := range vs {
				pairs++
				ue := proto.Equal(vs[i][0].(proto.Message), vs[j][0].(proto.Message))
				pe, ok := subjectEqual(vs[i][1].(pproto.Message), vs[j][1].(pproto.Message))
				if !ok || ue != pe {
					report("S8/equal-pair/"+tn, fmt.Sprintf("%%d~%%d", i, j), ue, pe)
				}
			}
		}
	}
	// Constructed values: typed nils of every type; nil elements.
%(TYPED)s
	ref := "unrecorded"
	if sec8RefBit == 0 {
		ref = "U+0020"
	} else if sec8RefBit == 1 {
		ref = "U+00A0"
	}
	subj := "unrecorded"
	if sec8SubjBit == 0 {
		subj = "U+0020"
	} else if sec8SubjBit == 1 {
		subj = "U+00A0"
	}
	fmt.Printf("ok  Section 8           %%d inputs (%%d corpus + generated + recursion edges + constructed), %%d Equal pairs; reference prefix %%s, subject prefix %%s\n",
		sec8Checks, %(NCORPUS)d, pairs, ref, subj)
}
'''

EQUAL_PRESENT = '''func subjectEqual(a, b pproto.Message) (bool, bool) {
	return pproto.Equal(a, b), true
}'''
EQUAL_ABSENT = '''// The subject proto package declares NO Equal (pre-route-A tree): every
// Equal comparison is a disagreement.
func subjectEqual(a, b pproto.Message) (bool, bool) {
	return false, false
}'''
ERROR_PRESENT = '''func subjectIsError(e error) bool {
	return errors.Is(e, pproto.Error)
}'''
ERROR_ABSENT = '''// The subject proto package declares NO Error sentinel (pre-route-A
// tree): errors.Is(err, proto.Error) cannot hold.
func subjectIsError(e error) bool {
	return false
}'''


def message_fields(msgs, enums, name, classify_field, refuse):
    fields = []
    for fname, ftype, ftag in msgs[name].fields:
        kind, num = classify_field(msgs, enums, name, fname, ftype, ftag)
        fields.append((num, fname, ftype, kind))
    fields.sort()
    return fields


def gen_go(msgs, enums, classify_field, refuse, proto_src):
    def mf(m, e, name):
        return message_fields(m, e, name, classify_field, refuse)
    return _gen_go(msgs, enums, mf, refuse, proto_src)


def _gen_go(msgs, enums, message_fields, refuse, proto_src):
    corpus = load_corpus(refuse)
    gen = battery(msgs, enums, message_fields)
    inputs = corpus + gen
    names = [n for n, _t, _h in inputs]
    if len(set(names)) != len(names):
        dup = sorted({n for n in names if names.count(n) > 1})
        refuse("section 8: duplicate input names: %s" % dup[:5])
    types = []
    for t in msgs:
        types.append('\t\t"%s": {"%s", func() proto.Message { return &up.%s{} }, '
                     'func() pproto.Message { return &pp.%s{} }},' % (t, t, t, t))
    rows = []
    for n, t, h in inputs:
        if h is None:
            rows.append('\t\t{%s, "%s", "", true},' % (json.dumps(n), t))
        else:
            rows.append('\t\t{%s, "%s", "%s", false},' % (json.dumps(n), t, h))
    typed = []
    for t in msgs:
        typed.append('\tsec8Typed(types["%s"], "typed-nil", (*up.%s)(nil), (*pp.%s)(nil))' % (t, t, t))
    # nil elements of every repeated message field
    for t in msgs:
        for num, fname, ftype, kind in message_fields(msgs, enums, t):
            if kind != "rep-msg":
                continue
            base = ftype.lstrip("*[]")
            typed.append('\tsec8Typed(types["%s"], "nil-elem-%s", &up.%s{%s: []*up.%s{nil}}, &pp.%s{%s: []*pp.%s{nil}})'
                         % (t, fname, t, fname, base, t, fname, base))
            typed.append('\tsec8Typed(types["%s"], "nil-and-empty-elem-%s", &up.%s{%s: []*up.%s{nil, {}}}, &pp.%s{%s: []*pp.%s{nil, {}}})'
                         % (t, fname, t, fname, base, t, fname, base))
            typed.append('\t{')
            typed.append('\t\tue := proto.Equal(&up.%s{%s: []*up.%s{nil}}, &up.%s{%s: []*up.%s{{}}})'
                         % (t, fname, base, t, fname, base))
            typed.append('\t\tpe, ok := subjectEqual(&pp.%s{%s: []*pp.%s{nil}}, &pp.%s{%s: []*pp.%s{{}}})'
                         % (t, fname, base, t, fname, base))
            typed.append('\t\tif !ok || ue != pe {')
            typed.append('\t\t\treport("S8/equal-nil-vs-empty-elem/%s", "%s", ue, pe)' % (t, fname))
            typed.append('\t\t}')
            typed.append('\t}')
    has_equal = "func Equal(" in proto_src
    has_error = "\nvar Error " in proto_src
    return GO_SEC8 % {
        "TYPES": "\n".join(types),
        "INPUTS": "\n".join(rows),
        "TYPED": "\n".join(typed),
        "NCORPUS": len(corpus),
        "EQUAL_SHIM": EQUAL_PRESENT if has_equal else EQUAL_ABSENT,
        "ERROR_SHIM": ERROR_PRESENT if has_error else ERROR_ABSENT,
    }, len(inputs), len(corpus)
