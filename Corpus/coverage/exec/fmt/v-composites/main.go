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

// ---- DELTA-REVIEW CRITICAL-1: the two RO flags are NOT one flag.
// reflect distinguishes flagStickyRO from flagEmbedRO, and only
// `Value.Field` treats them differently (reflect/value.go):
//
//	fl := v.flag&(flagStickyRO|flagIndir|flagAddr) | flag(typ.Kind())
//	if !field.name.IsExported() {
//	    if field.embedded() { fl |= flagEmbedRO } else { fl |= flagStickyRO }
//	}
//
// So descending through a struct field inherits ONLY the sticky bit.
// `CanInterface()` (which is what gates fmt's handleMethods at depth)
// tests flagRO = sticky|embed, so an EMBEDDED unexported field is
// method-suppressed AT ITS OWN LEVEL yet its children start clean.
// Every OTHER descent (Index/Elem/MapIndex) goes through `flag.ro()`,
// which COLLAPSES either bit to sticky — so a slice under an embedded
// unexported field does taint its elements. The renderer had one
// `tainted` bool for both, over-suppressing whole embedded subtrees.
//
// gc ground truth (2026-08-22, .tmp/deltarev/{v1,v6,w3,x1,p1..p7}):
//
//	embedded-unexported struct, exported Stringer field   {{E<4>}}
//	  same under %+v                                      {inner:{A:E<4>}}
//	two-level embedded-unexported                         {{{E<4>}}}
//	unexported NON-embedded above an embed (sticky wins)  {{{4}}}
//	unexported non-embedded leaf UNDER an embed           {{4}}
//	named-slice type embedded unexported (ro() collapse)  {[5 6]}
//	EXPORTED slice field under an embed                   {{[E<5> E<6>]}}
//	method at the embedded level, promotion ambiguous     {{E<4>} {E<5>}}
//	exported-embedded Mid over unexported-embedded deep   {{E<1> {E<2>}}}
//
// The rows below pin all nine. The `emb-formatter-below` row is the
// REFUSAL leg (red at frontend-export by design): a Formatter reached
// below an embedded unexported field IS consulted by gc ({{FMT:v:1}}),
// and the renderer does not model Format — so it must refuse there
// exactly as it refuses at an untainted level, never render `{{1}}`. ----

type embInner struct{ A strE }

type embOuter struct{ embInner }

func vEmbedStringerField() string {
	return fmt.Sprintf("%v|%+v", embOuter{embInner{4}}, embOuter{embInner{4}})
}

type embDeep2 struct{ C strE }

type embMid2 struct{ embDeep2 }

type embOuter2 struct{ embMid2 }

func vEmbedTwoLevel() string {
	return fmt.Sprintf("%v", embOuter2{embMid2{embDeep2{4}}})
}

// STICKY BEATS EMBED: the unexported non-embedded `m` taints the whole
// subtree, so the embedded level below it inherits sticky and its
// exported leaf still renders raw.
type embSticky struct{ m embMid2 }

func vEmbedStickyOverEmbed() string {
	return fmt.Sprintf("%v", embSticky{m: embMid2{embDeep2{4}}})
}

// An unexported NON-embedded leaf under an embedded level: sticky is
// set at the leaf itself, so raw.
type embInnerUnexp struct{ a strE }

type embOuter3 struct{ embInnerUnexp }

func vEmbedUnexportedLeaf() string {
	return fmt.Sprintf("%v", embOuter3{embInnerUnexp{4}})
}

// The ro() collapse: a NAMED SLICE type embedded unexported. The field
// level is embed-RO; Index() collapses that to sticky, so the elements
// are raw even though they are "one level below an embed".
type embEs []strE

type embOuter4 struct{ embEs }

func vEmbedNamedSliceType() string {
	return fmt.Sprintf("%v", embOuter4{embEs{5, 6}})
}

// The complement: an EXPORTED slice field under the embedded level.
// The field inherits sticky=0, so its elements are clean and the
// Stringer IS consulted.
type embInnerSl struct{ Ss []strE }

type embOuter5 struct{ embInnerSl }

func vEmbedExportedSlice() string {
	return fmt.Sprintf("%v", embOuter5{embInnerSl{[]strE{5, 6}}})
}

// THE DECISIVE ROW for "level only": both embedded types carry String,
// so the promotion into embOuter6 is AMBIGUOUS and embOuter6 has no
// String of its own. gc therefore reaches each embedded field with
// flagEmbedRO set — CanInterface() is false, the field's own String is
// NOT consulted — and renders the struct, whose exported leaf IS
// consulted: `{{E<4>} {E<5>}}`.
type embM1 struct{ A strE }

func (embM1) String() string { return "M1" }

type embM2 struct{ B strE }

func (embM2) String() string { return "M2" }

type embOuter6 struct {
	embM1
	embM2
}

func vEmbedMethodAtLevel() string {
	return fmt.Sprintf("%v", embOuter6{embM1{4}, embM2{5}})
}

// Exported-embedded Mid carrying an exported leaf BESIDE an
// unexported-embedded deep: the exported path stays clean throughout.
type embDeep struct{ D strE }

type EmbMid struct {
	M strE
	embDeep
}

type embOuter7 struct{ EmbMid }

func vEmbedMid() string {
	return fmt.Sprintf("%v", embOuter7{EmbMid{M: 1, embDeep: embDeep{D: 2}}})
}

// ---- fail-closed boundary rows (red at frontend-export BY DESIGN) ----

// The Formatter REFUSAL leg of CRITICAL-1: `embFmt` implements
// fmt.Formatter and is reached through an embedded unexported field.
// gc consults Format there ({{FMT:v:1}}); the renderer does not model
// Format at all, so this subject must REFUSE at frontend-export. Before
// the flag split it rendered `{{1}}` — a silent wrong answer, the worst
// class. If this row ever goes green without Format being modeled, the
// suppression has re-widened.
type embFmt int

func (f embFmt) Format(s fmt.State, verb rune) {
	fmt.Fprintf(s, "FMT:%c:%d", verb, int(f))
}

type embFmtInner struct{ A embFmt }

type embFmtOuter struct{ embFmtInner }

func vEmbedFormatterBelow() string {
	return fmt.Sprintf("%v", embFmtOuter{embFmtInner{A: 1}})
}

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
		vUnexportedSliceTaint(), vEmbedStringerField(), vEmbedTwoLevel(),
		vEmbedStickyOverEmbed(), vEmbedUnexportedLeaf(),
		vEmbedNamedSliceType(), vEmbedExportedSlice(),
		vEmbedMethodAtLevel(), vEmbedMid(), vEmbedFormatterBelow())
}
