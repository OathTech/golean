#!/usr/bin/env python3
"""codeccheck.py — the plainpb CODEC battery, under BOTH oracles.

The W4.1 codec (raftpb/plain_codec.go + proto/proto.go, docs/raft-w41-log.md
item 1) carries a differential obligation against the REAL protobuf runtime —
that half is difftest.py section 7 and needs the Go module cache, which some
sandboxes deny. THIS instrument is the half that always runs: a stdlib-free
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
    field number 0, group wire types).

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
	if !rtMessage(&pb.Message{Type: &mt, To: u64(2), From: u64(1), Term: u64(4),
		LogTerm: u64(3), Index: u64(10), Commit: u64(8), Vote: u64(5),
		Reject: bl(true), RejectHint: u64(9), Context: []byte("c"),
		Entries: []*pb.Entry{{Term: u64(1), Index: u64(2), Data: []byte("x")}, {Term: u64(1), Index: u64(3)}},
		Snapshot: &pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: u64(7)}},
		Responses: []*pb.Message{{To: u64(9)}}}) {
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
	b, err = proto.Marshal(&pb.Message{Type: &mt, To: u64(2), From: u64(1),
		Entries:  []*pb.Entry{{Term: u64(1), Index: u64(2)}},
		Snapshot: &pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: u64(9)}}})
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

	return 0
}

func main() {
	println(codecBattery())
}
'''


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
    with open(os.path.join(prog, "main.go"), "w") as f:
        f.write(BATTERY)
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
                        "--function", "codecBattery", "--fuel", "30000000"],
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
    print("codeccheck: PASS — 38 checks, both oracles agree, verdict 0")


if __name__ == "__main__":
    main()
