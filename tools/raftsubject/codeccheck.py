#!/usr/bin/env python3
"""codeccheck.py — the plainpb CODEC battery, under BOTH oracles.

The generated codec (W4.1, docs/raft-w41-log.md item 1; route A S1 since
2026-10-04: raftpb/plain_wire.go + plain_codec.go + plain_clone.go +
proto/proto.go) carries a differential obligation against the REAL protobuf
runtime — that half is difftest.py sections 7-8 and needs the Go module cache,
which some sandboxes deny. THIS instrument is the half that always runs: a stdlib-free
battery over the DERIVED codec itself, executed

  1. under `go run` (GOPATH scratch — raftpb/proto have no imports beyond
     `errors`, so no module access is needed), and
  2. under THE MACHINE (native frontend export + `golean native-json-run`),

comparing the two verdicts. The battery checks, per value shape:

  * round trip: Unmarshal(Marshal(x)) equals x (EqualMessage — presence
    included; repeated fields have no presence, so nil/empty folds are
    admitted by the equality, exactly as proto.Equal admits them);
  * Size = len(Marshal);
  * HAND-VERIFIED GOLDENS: exact byte sequences computed from the protobuf
    wire spec by hand (varint edges included: 300, 2^40, MaxUint64);
  * decode-only paths: packed repeated varints, unknown-field skipping,
    singular-embedded-message merge, malformed-input errors (truncation,
    field number 0, group wire types);
  * ROUTE A (checks 39-51, 100-125): typed nils, Equal, the Unwrap
    sentinel, the recursion edges, and the imported corpus against
    protobuf-go's recorded outcomes (see ROUTE A ADDITIONS below).

The battery function returns 0 on success or the FAILING CHECK's id; the
script requires both oracles to answer 0 and to AGREE. A check id, not a
checksum, so a red run names its check.

    tools/raftsubject/codeccheck.py [--keep]

Needs `artifacts/nativefrontend` (GO111MODULE=off go build -o
artifacts/nativefrontend ./tools/nativefrontend) and `.lake/build/bin/golean`
(scripts/capped lake build golean). Uncapped — do not point it at anything
but this tree.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))

BATTERY = r'''package main

import (
	pb "raftpb"

	"proto"
)

func u64(v uint64) *uint64 { return &v }
func bl(v bool) *bool      { return &v }

func bytesEq(a, b []byte) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

// roundTripEntry and friends: Marshal, check Size, Unmarshal into a fresh
// value, compare with the generated structural equality.
func rtEntry(x *pb.Entry) bool {
	b, err := proto.Marshal(x)
	if err != nil || b == nil {
		return false
	}
	if proto.Size(x) != len(b) {
		return false
	}
	out := &pb.Entry{}
	if proto.Unmarshal(b, out) != nil {
		return false
	}
	return x.EqualMessage(out)
}

func rtMessage(x *pb.Message) bool {
	b, err := proto.Marshal(x)
	if err != nil || b == nil {
		return false
	}
	if proto.Size(x) != len(b) {
		return false
	}
	out := &pb.Message{}
	if proto.Unmarshal(b, out) != nil {
		return false
	}
	return x.EqualMessage(out)
}

func rtConfState(x *pb.ConfState) bool {
	b, err := proto.Marshal(x)
	if err != nil || b == nil {
		return false
	}
	if proto.Size(x) != len(b) {
		return false
	}
	out := &pb.ConfState{}
	if proto.Unmarshal(b, out) != nil {
		return false
	}
	return x.EqualMessage(out)
}

func rtConfChange(x *pb.ConfChange) bool {
	b, err := proto.Marshal(x)
	if err != nil || b == nil {
		return false
	}
	if proto.Size(x) != len(b) {
		return false
	}
	out := &pb.ConfChange{}
	if proto.Unmarshal(b, out) != nil {
		return false
	}
	return x.EqualMessage(out)
}

func rtConfChangeV2(x *pb.ConfChangeV2) bool {
	b, err := proto.Marshal(x)
	if err != nil || b == nil {
		return false
	}
	if proto.Size(x) != len(b) {
		return false
	}
	out := &pb.ConfChangeV2{}
	if proto.Unmarshal(b, out) != nil {
		return false
	}
	return x.EqualMessage(out)
}

func rtHardState(x *pb.HardState) bool {
	b, err := proto.Marshal(x)
	if err != nil || b == nil {
		return false
	}
	if proto.Size(x) != len(b) {
		return false
	}
	out := &pb.HardState{}
	if proto.Unmarshal(b, out) != nil {
		return false
	}
	return x.EqualMessage(out)
}

func rtSnapshot(x *pb.Snapshot) bool {
	b, err := proto.Marshal(x)
	if err != nil || b == nil {
		return false
	}
	if proto.Size(x) != len(b) {
		return false
	}
	out := &pb.Snapshot{}
	if proto.Unmarshal(b, out) != nil {
		return false
	}
	return x.EqualMessage(out)
}

// codecBattery returns 0, or the id of the first failing check.
func codecBattery() int {
	et := pb.EntryConfChange

	// ---- round trips + Size (checks 1..19) --------------------------------
	if !rtEntry(&pb.Entry{}) {
		return 1
	}
	if !rtEntry(&pb.Entry{Term: u64(0)}) { // present-but-zero emits
		return 2
	}
	if !rtEntry(&pb.Entry{Term: u64(5), Index: u64(7), Type: &et, Data: []byte("ab")}) {
		return 3
	}
	if !rtEntry(&pb.Entry{Data: []byte{}}) { // present-but-empty bytes
		return 4
	}
	if !rtEntry(&pb.Entry{Term: u64(1 << 40), Index: u64(^uint64(0))}) {
		return 5
	}
	if !rtHardState(&pb.HardState{}) {
		return 6
	}
	if !rtHardState(&pb.HardState{Term: u64(1), Vote: u64(2), Commit: u64(3)}) {
		return 7
	}
	if !rtConfState(&pb.ConfState{}) {
		return 8
	}
	if !rtConfState(&pb.ConfState{Voters: []uint64{1, 2, 3}, Learners: []uint64{4},
		VotersOutgoing: []uint64{5, 6}, LearnersNext: []uint64{7}, AutoLeave: bl(true)}) {
		return 9
	}
	if !rtConfState(&pb.ConfState{AutoLeave: bl(false)}) { // present-but-false
		return 10
	}
	if !rtConfChange(&pb.ConfChange{}) {
		return 11
	}
	cct := pb.ConfChangeAddNode
	if !rtConfChange(&pb.ConfChange{Type: &cct, NodeId: u64(300), Context: []byte("ctx"), Id: u64(1)}) {
		return 12
	}
	if !rtConfChangeV2(&pb.ConfChangeV2{}) {
		return 13
	}
	tr := pb.ConfChangeTransitionJointExplicit
	ccl := pb.ConfChangeAddLearnerNode
	if !rtConfChangeV2(&pb.ConfChangeV2{Transition: &tr,
		Changes: []*pb.ConfChangeSingle{{Type: &cct, NodeId: u64(3)}, {Type: &ccl, NodeId: u64(4)}},
		Context: []byte("q")}) {
		return 14
	}
	if !rtSnapshot(&pb.Snapshot{}) {
		return 15
	}
	if !rtSnapshot(&pb.Snapshot{Data: []byte("d"), Metadata: &pb.SnapshotMetadata{
		Index: u64(9), Term: u64(2), ConfState: &pb.ConfState{Voters: []uint64{1}}}}) {
		return 16
	}
	mt := pb.MsgApp
	if !rtMessage(&pb.Message{}) {
		return 17
	}
	// (The nested literals are HOISTED: the frontend's E13 (b) residual
	// quarantines a slice literal with a panicky payload followed by an
	// ordered call in the same statement — found 2026-10-04 by route A S1:
	// this battery's machine leg had gone red on main for that reason.)
	m18e1 := &pb.Entry{Term: u64(1), Index: u64(2), Data: []byte("x")}
	m18e2 := &pb.Entry{Term: u64(1), Index: u64(3)}
	m18es := []*pb.Entry{m18e1, m18e2}
	m18r := &pb.Message{To: u64(9)}
	m18rs := []*pb.Message{m18r}
	m18s := &pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: u64(7)}}
	if !rtMessage(&pb.Message{Type: &mt, To: u64(2), From: u64(1), Term: u64(4),
		LogTerm: u64(3), Index: u64(10), Commit: u64(8), Vote: u64(5),
		Reject: bl(true), RejectHint: u64(9), Context: []byte("c"),
		Entries: m18es, Snapshot: m18s, Responses: m18rs}) {
		return 18
	}
	if !rtMessage(&pb.Message{Reject: bl(false), Entries: []*pb.Entry{}}) {
		return 19
	}

	// ---- goldens (checks 20..27): bytes computed BY HAND from the wire
	// spec — field-number order, single-byte tags, base-128 varints.
	// (Style note: every call and slice literal is HOISTED out of
	// short-circuit operands — the frontend's E3 conditional
	// normalization refuses those shapes by design.)
	b, err := proto.Marshal(&pb.HardState{Term: u64(1), Vote: u64(2), Commit: u64(3)})
	want := []byte{0x08, 0x01, 0x10, 0x02, 0x18, 0x03}
	if err != nil {
		return 20
	}
	if !bytesEq(b, want) {
		return 20
	}
	// Entry fields in NUMBER order Type(1),Term(2),Index(3),Data(4) — not
	// struct order.
	b, err = proto.Marshal(&pb.Entry{Term: u64(5), Index: u64(7), Type: &et, Data: []byte("ab")})
	want = []byte{0x08, 0x01, 0x10, 0x05, 0x18, 0x07, 0x22, 0x02, 0x61, 0x62}
	if err != nil {
		return 21
	}
	if !bytesEq(b, want) {
		return 21
	}
	// varint edge 300 = 0xac 0x02; present-but-zero Type emits 10 00.
	zt := pb.ConfChangeAddNode
	b, err = proto.Marshal(&pb.ConfChange{Type: &zt, NodeId: u64(300)})
	want = []byte{0x10, 0x00, 0x18, 0xac, 0x02}
	if err != nil {
		return 22
	}
	if !bytesEq(b, want) {
		return 22
	}
	// repeated varint UNPACKED + trailing bool: ConfState{Voters:[1,2],AutoLeave:true}.
	b, err = proto.Marshal(&pb.ConfState{Voters: []uint64{1, 2}, AutoLeave: bl(true)})
	want = []byte{0x08, 0x01, 0x08, 0x02, 0x28, 0x01}
	if err != nil {
		return 23
	}
	if !bytesEq(b, want) {
		return 23
	}
	// nested messages with length prefixes.
	m24e := &pb.Entry{Term: u64(1), Index: u64(2)}
	m24es := []*pb.Entry{m24e}
	m24s := &pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: u64(9)}}
	b, err = proto.Marshal(&pb.Message{Type: &mt, To: u64(2), From: u64(1),
		Entries: m24es, Snapshot: m24s})
	want = []byte{
		0x08, 0x03, 0x10, 0x02, 0x18, 0x01,
		0x3a, 0x04, 0x10, 0x01, 0x18, 0x02,
		0x4a, 0x04, 0x12, 0x02, 0x10, 0x09}
	if err != nil {
		return 24
	}
	if !bytesEq(b, want) {
		return 24
	}
	// varint edges: 2^40 and MaxUint64 (10-byte encoding).
	b, err = proto.Marshal(&pb.HardState{Term: u64(1 << 40)})
	want = []byte{0x08, 0x80, 0x80, 0x80, 0x80, 0x80, 0x20}
	if err != nil {
		return 25
	}
	if !bytesEq(b, want) {
		return 25
	}
	b, err = proto.Marshal(&pb.HardState{Term: u64(^uint64(0))})
	want = []byte{0x08, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01}
	if err != nil {
		return 26
	}
	if !bytesEq(b, want) {
		return 26
	}
	// empty message marshals to zero-length NON-NIL (proto.Marshal contract).
	b, err = proto.Marshal(&pb.ConfChangeV2{})
	if err != nil {
		return 27
	}
	if b == nil {
		return 27
	}
	if len(b) != 0 {
		return 27
	}

	// ---- decode-only paths (checks 28..35) --------------------------------
	// packed repeated varints are ACCEPTED though never emitted.
	cs := &pb.ConfState{}
	packed := []byte{0x0a, 0x03, 0x01, 0x02, 0x03}
	if proto.Unmarshal(packed, cs) != nil {
		return 28
	}
	if len(cs.Voters) != 3 {
		return 28
	}
	if cs.Voters[0] != 1 {
		return 28
	}
	if cs.Voters[2] != 3 {
		return 28
	}
	// unknown field (num 15, varint) skipped; known field after it lands.
	hs := &pb.HardState{}
	unk := []byte{0x78, 0x2a, 0x08, 0x07}
	if proto.Unmarshal(unk, hs) != nil {
		return 29
	}
	if hs.Term == nil {
		return 29
	}
	if *hs.Term != 7 {
		return 29
	}
	if hs.Vote != nil {
		return 29
	}
	// singular embedded message occurring twice MERGES.
	sn := &pb.Snapshot{}
	twice := []byte{0x12, 0x02, 0x10, 0x01, 0x12, 0x02, 0x18, 0x02}
	if proto.Unmarshal(twice, sn) != nil {
		return 30
	}
	if sn.Metadata == nil {
		return 30
	}
	if sn.Metadata.GetIndex() != 1 {
		return 30
	}
	if sn.Metadata.GetTerm() != 2 {
		return 30
	}
	// proto.Unmarshal RESETS the destination first.
	hs2 := &pb.HardState{Vote: u64(9)}
	seven := []byte{0x08, 0x07}
	if proto.Unmarshal(seven, hs2) != nil {
		return 31
	}
	if hs2.Vote != nil {
		return 31
	}
	if *hs2.Term != 7 {
		return 31
	}
	// malformed: truncated varint; field number 0; group wire type.
	trunc := []byte{0x08}
	if proto.Unmarshal(trunc, &pb.HardState{}) == nil {
		return 32
	}
	zeroNum := []byte{0x00}
	if proto.Unmarshal(zeroNum, &pb.HardState{}) == nil {
		return 33
	}
	group := []byte{0x7b} // num 15, wire 3
	if proto.Unmarshal(group, &pb.HardState{}) == nil {
		return 34
	}
	// scalar last-one-wins with a fresh cell.
	hs3 := &pb.HardState{}
	lastWins := []byte{0x08, 0x01, 0x08, 0x02}
	if proto.Unmarshal(lastWins, hs3) != nil {
		return 35
	}
	if *hs3.Term != 2 {
		return 35
	}

	// ---- the raft shapes (checks 36..38) ----------------------------------
	// the stepLeader shape: ConfChange bytes inside an Entry round-trip
	// through MarshalConfChange and back out of Entry.Data.
	cc := &pb.ConfChange{Type: &cct, NodeId: u64(2), Context: []byte("cc")}
	typ, data, mcErr := pb.MarshalConfChange(cc)
	if mcErr != nil {
		return 36
	}
	if typ != pb.EntryConfChange {
		return 36
	}
	ent := &pb.Entry{Type: &et, Data: data}
	ccOut := &pb.ConfChange{}
	if proto.Unmarshal(ent.GetData(), ccOut) != nil {
		return 37
	}
	if !cc.EqualMessage(ccOut) {
		return 37
	}
	// entsSize's shape: Size over entries.
	e1 := &pb.Entry{Term: u64(1), Index: u64(2), Data: []byte("x")}
	e2 := &pb.Entry{Term: u64(1), Index: u64(3)}
	if proto.Size(e1) != 7 {
		return 38
	}
	if proto.Size(e2) != 4 {
		return 38
	}

	// ---- route A (checks 39..): typed nils, Equal, the sentinel, and the
	// imported corpus — generated below (codeccheck.py ROUTE_A_GO).
	if r := routeABattery(); r != 0 {
		return r
	}
	return 0
}

func main() {
	println(codecBattery())
}
'''


# ---- ROUTE A additions (docs/2026-10-04_route-a-protobuf-design.md D9) ----
#
# Checks 39-41: the typed-nil behaviours of proto.Marshal / Size / Clone
# (proto/encode.go:141-146, size.go:19-35, merge.go:55-57). Checks 42-46:
# proto.Equal (the subject declares it since route A; on a tree without it
# the battery answers 42 — red, never skipped). Check 47: the error value
# unwraps to the proto.Error sentinel (errors.Is itself is refused on the
# machine by name, FR-14 — D10 — so the battery checks Unwrap directly;
# absent sentinel -> 47). Checks 100+k: entry k of the imported 26-entry
# corpus (tools/raftsubject/fixtures/i6-malformed-conf-bytes.json) against
# protobuf-go's OWN outcome (fixtures/i6-reference-protobuf-go-v1.36.11.json,
# written by `difftest.py --emit-reference`): verdict, error text modulo the
# per-binary prefix (MEMBERSHIP over the two spellings), Size, and the
# re-Marshal bytes (non-nil for a decoded message).

REFERENCE = os.path.join(HERE, "fixtures", "i6-reference-protobuf-go-v1.36.11.json")
CORPUS = os.path.join(HERE, "fixtures", "i6-malformed-conf-bytes.json")
CORPUS_SHA256 = "cd724c9b40a96879c024ffe5b0c8f494c44ff2fe87a59484c15f6d19ebca5dd9"


NEST_GO = """// nestResponses: d nested Message.responses (field 14) levels, built in
// O(total) — the lengths first, then the prefixes outermost-first.
func nestResponses(d int) []byte {
	lens := make([]int, d+1)
	for k := 1; k <= d; k++ {
		inner := lens[k-1]
		w := 1
		for v := inner; v >= 0x80; v >>= 7 {
			w++
		}
		lens[k] = 1 + w + inner
	}
	b := make([]byte, 0, lens[d])
	for k := d; k >= 1; k-- {
		b = append(b, 0x72)
		v := lens[k-1]
		for v >= 0x80 {
			b = append(b, byte(v)|0x80)
			v >>= 7
		}
		b = append(b, byte(v))
	}
	return b
}

// nestGroups: d nested unknown groups of field 15.
func nestGroups(d int) []byte {
	b := make([]byte, 0, 2*d)
	for k := 0; k < d; k++ {
		b = append(b, 0x7b)
	}
	for k := 0; k < d; k++ {
		b = append(b, 0x7c)
	}
	return b
}
"""

# The machine leg's fuel: the recursion edges (checks 48..51) need
# 10M-40M steps each (measured 2026-10-04).
MACHINE_FUEL = "300000000"


def go_bytes(h):
    if not h:
        return "[]byte{}"
    return "[]byte{" + ", ".join("0x%02x" % c for c in bytes.fromhex(h)) + "}"


def route_a_go(proto_src):
    import hashlib
    raw = open(CORPUS, "rb").read()
    if hashlib.sha256(raw).hexdigest() != CORPUS_SHA256:
        sys.exit("codeccheck.py: the imported corpus changed (frozen; fail closed)")
    corpus = json.loads(raw)["entries"]
    ref = json.load(open(REFERENCE))
    refs = {e["name"]: e for e in ref["entries"]}
    if len(corpus) != 26 or len(refs) != 26:
        sys.exit("codeccheck.py: corpus/reference size mismatch (%d/%d)" % (len(corpus), len(refs)))
    has_equal = "func Equal(" in proto_src
    has_error = "\nvar Error " in proto_src
    g = ["func routeABattery() int {",
         "\t// typed nils (checks 39..41)",
         "\tvar tn *pb.Entry",
         "\tnb, nerr := proto.Marshal(tn)",
         "\tif nerr != nil {",
         "\t\treturn 39",
         "\t}",
         "\tif nb != nil {",
         "\t\treturn 39",
         "\t}",
         "\tif proto.Size(tn) != 0 {",
         "\t\treturn 40",
         "\t}",
         "\tnc := proto.Clone(tn)",
         "\tif nc == nil {",
         "\t\treturn 41",
         "\t}",
         "\tif nc.(*pb.Entry) != nil {",
         "\t\treturn 41",
         "\t}"]
    if has_equal:
        g += ["\t// proto.Equal (checks 42..46)",
              "\tx := &pb.Entry{Term: u64(3), Data: []byte(\"q\")}",
              "\tif !proto.Equal(x, proto.Clone(x)) {",
              "\t\treturn 42",
              "\t}",
              "\tif proto.Equal(&pb.Entry{}, tn) {",
              "\t\treturn 43",
              "\t}",
              "\tif !proto.Equal(nil, nil) {",
              "\t\treturn 44",
              "\t}",
              "\tua := &pb.HardState{}",
              "\tub := &pb.HardState{}",
              "\tab := []byte{0x78, 0x01, 0x80, 0x01, 0x02}",
              "\tba := []byte{0x80, 0x01, 0x02, 0x78, 0x01}",
              "\tif proto.Unmarshal(ab, ua) != nil {",
              "\t\treturn 45",
              "\t}",
              "\tif proto.Unmarshal(ba, ub) != nil {",
              "\t\treturn 45",
              "\t}",
              "\tif !proto.Equal(ua, ub) {",
              "\t\treturn 45",
              "\t}",
              "\tuc := &pb.HardState{}",
              "\txy := []byte{0x78, 0x01, 0x78, 0x02}",
              "\tif proto.Unmarshal(xy, uc) != nil {",
              "\t\treturn 46",
              "\t}",
              "\tud := &pb.HardState{}",
              "\tyx := []byte{0x78, 0x02, 0x78, 0x01}",
              "\tif proto.Unmarshal(yx, ud) != nil {",
              "\t\treturn 46",
              "\t}",
              "\tif proto.Equal(uc, ud) {",
              "\t\treturn 46",
              "\t}"]
    else:
        g += ["\t// the subject proto declares NO Equal (pre-route-A tree): red",
              "\treturn 42"]
    if has_error:
        g += ["\t// the sentinel (check 47)",
              "\tserr := proto.Unmarshal([]byte{0x00}, &pb.HardState{})",
              "\tif serr == nil {",
              "\t\treturn 47",
              "\t}",
              "\tuw, uok := serr.(interface{ Unwrap() error })",
              "\tif !uok {",
              "\t\treturn 47",
              "\t}",
              "\tif uw.Unwrap() != proto.Error {",
              "\t\treturn 47",
              "\t}"]
    else:
        g += ["\t// the subject proto declares NO Error sentinel (pre-route-A tree): red",
              "\treturn 47"]
    if has_error:
        # The recursion edges (checks 48..51; design D4, Q3 [USER]
        # 2026-10-04): 10000 nested messages (the top one included) decode,
        # 10001 is errRecursionDepth; 10001 nested unknown groups skip,
        # 10002 is errDecode. Each edge costs 10M-40M machine steps — past
        # the corpus strict lane's 10M fuel, so the edges live HERE (the
        # machine leg runs with --fuel MACHINE_FUEL) and in difftest.py
        # section 8 (exact vs protobuf-go).
        g += ["\t// the recursion edges (checks 48..51)",
              "\tif proto.Unmarshal(nestResponses(9999), &pb.Message{}) != nil {",
              "\t\treturn 48",
              "\t}",
              "\trerr := proto.Unmarshal(nestResponses(10000), &pb.Message{})",
              "\tif rerr == nil {",
              "\t\treturn 49",
              "\t}",
              "\trt := rerr.Error()",
              "\tif rt != \"proto: exceeded maximum recursion depth\" {",
              "\t\tif rt != \"proto:\\u00a0exceeded maximum recursion depth\" {",
              "\t\t\treturn 49",
              "\t\t}",
              "\t}",
              "\tif proto.Unmarshal(nestGroups(10001), &pb.Message{}) != nil {",
              "\t\treturn 50",
              "\t}",
              "\tgerr := proto.Unmarshal(nestGroups(10002), &pb.Message{})",
              "\tif gerr == nil {",
              "\t\treturn 51",
              "\t}",
              "\tgt := gerr.Error()",
              "\tif gt != \"proto: cannot parse invalid wire-format data\" {",
              "\t\tif gt != \"proto:\\u00a0cannot parse invalid wire-format data\" {",
              "\t\t\treturn 51",
              "\t\t}",
              "\t}"]
    g += ["\t// the imported corpus (checks 100..125)"]
    for k, e in enumerate(corpus):
        r = refs.get("corpus/" + e["name"])
        if r is None:
            sys.exit("codeccheck.py: no reference outcome for corpus entry %s" % e["name"])
        cid = 100 + k
        typ = "ConfChange" if e["kind"] == "v1" else "ConfChangeV2"
        data = "nil" if e["data"] is None else go_bytes(e["data"])
        v = "c%d" % k
        g += ["\t// %d: %s" % (cid, e["name"]),
              "\t%sm := &pb.%s{}" % (v, typ),
              "\tvar %sd []byte = %s" % (v, data),
              "\t%serr := proto.Unmarshal(%sd, %sm)" % (v, v, v)]
        if r["verdict"] == "ok":
            g += ["\tif %serr != nil {" % v, "\t\treturn %d" % cid, "\t}"]
        else:
            g += ["\tif %serr == nil {" % v, "\t\treturn %d" % cid, "\t}",
                  "\t%st := %serr.Error()" % (v, v),
                  "\tif %st != \"proto: %s\" {" % (v, r["text"]),
                  "\t\tif %st != \"proto:\\u00a0%s\" {" % (v, r["text"]),
                  "\t\t\treturn %d" % cid,
                  "\t\t}",
                  "\t}"]
        g += ["\tif proto.Size(%sm) != %d {" % (v, r["size"]), "\t\treturn %d" % cid, "\t}",
              "\t%sb, %sme := proto.Marshal(%sm)" % (v, v, v),
              "\tif %sme != nil {" % v, "\t\treturn %d" % cid, "\t}",
              "\tif %sb == nil {" % v, "\t\treturn %d" % cid, "\t}",
              "\tif !bytesEq(%sb, %s) {" % (v, go_bytes(r["marshal"])), "\t\treturn %d" % cid, "\t}"]
    g += ["\treturn 0", "}", "", NEST_GO]
    return "\n".join(g) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--out", default=os.path.join(REPO, "artifacts", "codeccheck"))
    ap.add_argument("--frontend", default=os.path.join(REPO, "artifacts", "nativefrontend"))
    ap.add_argument("--golean", default=os.path.join(REPO, ".lake", "build", "bin", "golean"))
    args = ap.parse_args()

    for tool, hint in ((args.frontend, "GO111MODULE=off go build -o artifacts/nativefrontend ./tools/nativefrontend"),
                       (args.golean, "scripts/capped lake build golean")):
        if not os.path.exists(tool):
            sys.exit("codeccheck.py: missing %s (build it: %s)" % (tool, hint))

    out = args.out
    shutil.rmtree(out, ignore_errors=True)
    # One program tree, used by both oracles: main.go + raftpb/ + proto/ is
    # exactly the frontend's case-local layout; for go run the same packages
    # are exposed through a GOPATH src/ symlink-free copy.
    prog = os.path.join(out, "prog")
    os.makedirs(prog)
    for pkg in ("raftpb", "proto"):
        shutil.copytree(os.path.join(REPO, "raftsubject", pkg), os.path.join(prog, pkg))
    proto_src = open(os.path.join(REPO, "raftsubject", "proto", "proto.go")).read()
    with open(os.path.join(prog, "main.go"), "w") as f:
        f.write(BATTERY)
        f.write("\n" + route_a_go(proto_src))
    gopath = os.path.join(out, "gopath")
    os.makedirs(os.path.join(gopath, "src"))
    for pkg in ("raftpb", "proto"):
        shutil.copytree(os.path.join(prog, pkg), os.path.join(gopath, "src", pkg))

    env = dict(os.environ)
    env["GOCACHE"] = os.path.join(REPO, "artifacts", "go-build-cache")
    env["GO111MODULE"] = "off"
    env["GOPATH"] = gopath
    r = subprocess.run(["go", "run", "main.go"], cwd=prog, env=env,
                       capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit("codeccheck.py: go run failed:\n%s%s" % (r.stdout, r.stderr))
    # The battery prints with builtin println, which writes to STDERR (the
    # battery avoids fmt on purpose — fmt is not modeled).
    go_verdict = r.stderr.strip()
    print("codeccheck: go run verdict: %s" % go_verdict)

    wire = os.path.join(out, "wire.json")
    r = subprocess.run([args.frontend, "--dir", prog, "--out", wire],
                       capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit("codeccheck.py: frontend export failed:\n%s" % r.stderr)
    r = subprocess.run([args.golean, "native-json-run", "--input", wire,
                        "--function", "codecBattery", "--fuel", MACHINE_FUEL],
                       capture_output=True, text=True)
    if r.returncode != 0 and not r.stdout.strip():
        sys.exit("codeccheck.py: machine run failed:\n%s" % r.stderr)
    try:
        obs = json.loads(r.stdout.strip().splitlines()[-1])
    except (ValueError, IndexError):
        sys.exit("codeccheck.py: unreadable machine observation:\n%s%s" % (r.stdout, r.stderr))
    if obs.get("status") != "ok" or len(obs.get("values", [])) != 1:
        sys.exit("codeccheck.py: machine verdict is not a clean value: %s" % r.stdout.strip())
    machine_verdict = str(obs["values"][0].get("value"))
    print("codeccheck: machine verdict: %s" % machine_verdict)

    if not args.keep:
        shutil.rmtree(out, ignore_errors=True)
    if go_verdict != machine_verdict:
        sys.exit("codeccheck.py: ORACLES DISAGREE (go=%s machine=%s)"
                 % (go_verdict, machine_verdict))
    if go_verdict != "0":
        sys.exit("codeccheck.py: battery check %s FAILED under both oracles"
                 % go_verdict)
    print("codeccheck: PASS — checks 1-51 + the 26 imported corpus entries (100-125), both oracles agree, verdict 0")


if __name__ == "__main__":
    main()
