package main

// %v / %+v COMPOSITE rendering pins (W4.3 item 1, the rendered tier —
// docs/raft-w43-log.md). The modeled composite subset is recursive over
// the STATIC type at emit time: slices and named structs whose
// leaves are the already-modeled scalar kinds (ints, string, bool) or
// error/Stringer implementors (consulted per element/field, as gc's
// printValue does at depth). Everything outside — maps, pointers,
// interfaces-at-depth, anonymous structs — refuses per-declaration
// (fail closed; the two boundary rows at the bottom pin that).
//
// gc probes: artifacts/w43/probe-fmt (A1-A4, B1-B2, C1-C2, D1-D4).
// Raft shapes pinned: DescribeConfState's %v over []uint64;
// DescribeReady's "ReadStates %v" over []ReadState (struct with a
// []byte field — bytes render as decimal lists under %v);
// logSlice.valid's %+v over entryID.

import "fmt"

type readState struct {
	Index      uint64
	RequestCtx []byte
}

type entryID struct {
	term  uint64
	index uint64
}

type st8 uint64

func (s st8) String() string {
	if s == 0 {
		return "Z"
	}
	return "STR<" + string(rune('0'+int(s%10))) + ">"
}

type panickyElem int32

func (p panickyElem) String() string { panic("elem stub") }

type namedU64s []uint64

func vSliceUint64() string {
	var nilsl []uint64
	return fmt.Sprintf("a=%v b=%v c=%v d=%v",
		[]uint64{1, 2, 3}, []uint64{}, nilsl, []uint64{42})
}

// The DescribeConfState format verbatim (4 slices + %v over bool).
func vConfStateShape() string {
	return fmt.Sprintf(
		"Voters:%v VotersOutgoing:%v Learners:%v LearnersNext:%v AutoLeave:%v",
		[]uint64{1, 2, 3}, []uint64{}, []uint64{4}, []uint64{}, false)
}

func vStruct() string {
	return fmt.Sprintf("%v", entryID{term: 3, index: 9})
}

func plusVStruct() string {
	return fmt.Sprintf("entry %+v here", entryID{term: 3, index: 9})
}

func vSliceStructBytes() string {
	return fmt.Sprintf("ReadStates %v\n",
		[]readState{{5, []byte("rc")}, {7, nil}})
}

func plusVSliceStruct() string {
	return fmt.Sprintf("%+v", []readState{{5, []byte("rc")}, {7, nil}})
}

func vStringerElems() string {
	return fmt.Sprintf("%v|%+v", []st8{1, 2}, []st8{3, 0})
}

func vStringerElemPanic() string {
	return fmt.Sprintf("%v", []panickyElem{4})
}

type wrapS struct{ S st8 }

func plusVStringerField() string {
	return fmt.Sprintf("%+v %v", wrapS{S: 4}, wrapS{S: 0})
}

func vNamedSlice() string {
	return fmt.Sprintf("%v", namedU64s{8, 9})
}

func vNestedStruct() string {
	return fmt.Sprintf("%+v", struct2{E: entryID{1, 2}, N: 5})
}

type struct2 struct {
	E entryID
	N uint64
}

// ---- fail-closed boundary rows (red at frontend-export BY DESIGN) ----

func vMapOutside() string {
	return fmt.Sprintf("%v", map[uint64]bool{1: true})
}

func vPtrFieldOutside() string {
	n := 5
	return fmt.Sprintf("%v", struct3{P: &n})
}

type struct3 struct{ P *int }

func main() {
	println(vSliceUint64(), vConfStateShape(), vStruct(), plusVStruct(),
		vSliceStructBytes(), plusVSliceStruct(), vStringerElems(),
		vStringerElemPanic(), plusVStringerField(), vNamedSlice(),
		vNestedStruct(), vMapOutside(), vPtrFieldOutside())
}
