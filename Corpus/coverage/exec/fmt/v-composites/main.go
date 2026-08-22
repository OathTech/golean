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

// ---- R1-F1/R4-C-2 (W4.3 audit fix round): UNEXPORTED fields stop
// method consultation for their whole SUBTREE — gc (via reflect) can
// not call methods on values reached through an unexported field, so
// it renders them RAW; the composite renderer consulted Stringer on
// every field regardless (machine `{E<1> E<2>}` where gc says
// `{E<1> 2}`). gc-probed: .tmp/fixround-probes/f1 — `{E<1> 2}`,
// `{A:E<1> b:2}`, `{{3} E<4>}`, `{in:{X:3} A:E<4>}`, `{[5 6]}`. ----

type strE int

func (e strE) String() string { return "E<" + string(rune('0'+int(e))) + ">" }

type mixedExp struct {
	A strE // exported: Stringer consulted
	b strE // unexported: RAW (2, not E<2>)
}

func vUnexportedStringerField() string {
	return fmt.Sprintf("%v|%+v", mixedExp{1, 2}, mixedExp{1, 2})
}

type innerX struct{ X strE }

type taintOuter struct {
	in innerX // unexported STRUCT field: the whole subtree renders raw
	A  strE   // exported control BESIDE the taint: still E<4>
}

func vUnexportedSubtreeTaint() string {
	return fmt.Sprintf("%v|%+v", taintOuter{innerX{3}, 4}, taintOuter{innerX{3}, 4})
}

type taintSlice struct {
	bs []strE // unexported SLICE field: elements render raw too
}

func vUnexportedSliceTaint() string {
	return fmt.Sprintf("%v|%+v", taintSlice{[]strE{5, 6}}, taintSlice{[]strE{5, 6}})
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
		vNestedStruct(), vMapOutside(), vPtrFieldOutside(),
		vUnexportedStringerField(), vUnexportedSubtreeTaint(),
		vUnexportedSliceTaint())
}
