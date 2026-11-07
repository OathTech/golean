package main

// Sweep lane sweep/s22-readout (2026-11-07), shape S22 — the readout (the matrix is on the member entries'
// Neighbourhood lines in docs/BUGS.md, BUG-019 and BUG-013 above all; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group A7: the struct observation's typeName and field names beside the two pinned renderings (the anonymous
// empty struct's "" — BUG-019 — and the instantiation's bracketed name — BUG-013).

type Every struct {
	B  bool
	I8 int8
	U  uint64
	F  float32
	S  string
	A  [2]int
}
type Inner struct{ N int }
type Outer struct {
	In  Inner
	Arr [1]Inner
}
type Embeds struct {
	Inner
	Tag string
}
type Unexported struct {
	visible int
	Hidden  string
}
type Blank struct {
	A int
	_ int
	B int
}
type Shape interface{ Area() int }
type Sq struct{ L int }

func (s Sq) Area() int { return s.L * s.L }

type IfaceFields struct {
	Any   any
	Shape Shape
	Err   error
}
type Named struct{ V int }
type Alias = Named
type WithArray struct{ Cells [3]string }
type Box[T any] struct{ V T }
type Empty struct{}

func everyFieldKind() Every { return Every{true, -8, 18446744073709551615, 0.5, "s", [2]int{1, 2}} }
func nested() Outer         { return Outer{In: Inner{1}, Arr: [1]Inner{{2}}} }
func embeddedValue() Embeds { return Embeds{Inner{7}, "t"} }
func unexportedField() Unexported {
	return Unexported{visible: 3, Hidden: "h"}
}
func blankField() Blank { return Blank{A: 1, B: 2} }
func interfaceFields() (IfaceFields, IfaceFields) {
	return IfaceFields{}, IfaceFields{Any: 5, Shape: Sq{3}, Err: nil}
}
func aliasOfStruct() (Alias, Named) { return Alias{1}, Named{2} }
func localStructType() any {
	type local struct{ Q int }
	return local{9}
}
func arrayField() WithArray                  { return WithArray{[3]string{"a", "b", "c"}} }
func emptyStructInBox() (Box[struct{}], any) { return Box[struct{}]{}, Box[struct{}]{} }
func namedEmptyInBox() (Box[Empty], any)     { return Box[Empty]{}, Box[Empty]{} }

func main() {
	everyFieldKind()
	nested()
	embeddedValue()
	unexportedField()
	blankField()
	interfaceFields()
	aliasOfStruct()
	localStructType()
	arrayField()
	emptyStructInBox()
	namedEmptyInBox()
}
