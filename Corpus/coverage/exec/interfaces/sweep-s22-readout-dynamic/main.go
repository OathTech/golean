package main

// Sweep lane sweep/s22-readout (2026-11-07), shape S22 — the readout (the matrix is on the member entries'
// Neighbourhood lines in docs/BUGS.md; the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Group A8: the `dynamic` field names the dynamic type as reflect.Type.Name() does — unqualified, the bracket of an
// instantiation spelled with package-qualified arguments (BUG-013's shape), "" never (a nil box observes as nil).

type K8 int8
type K64 int64
type U32 uint32
type S string
type Flag bool
type F32 float32
type P struct{ X int }
type E struct{ Msg string }

func (e E) Error() string { return e.Msg }

type Shape interface{ Area() int }
type Sq struct{ L int }

func (s Sq) Area() int { return s.L * s.L }

type Box[T any] struct{ V T }
type Pair[A, B any] struct {
	A A
	B B
}

func definedIntKinds() (any, any, any)  { return K8(-1), K64(2), U32(3) }
func definedStringBool() (any, any)     { return S("s"), Flag(true) }
func definedFloat() any                 { return F32(1.5) }
func structAndNil() (any, any, [2]any)  { return P{1}, nil, [2]any{P{2}, nil} }
func errorResults() (error, error, any) { return nil, E{"m"}, E{"boxed"} }
func nonemptyInterfaceResult() (Shape, Shape) {
	var s Shape = Sq{3}
	return s, nil
}
func instantiationBoxes() (any, any, any) {
	return Box[int]{1}, Box[S]{"s"}, Pair[K8, string]{1, "p"}
}
func boxInBox() (any, any) { return Box[Box[int]]{Box[int]{2}}, Box[Pair[int, P]]{} }

type A2 [2]Box[Flag]

func namedArrayDynamic() (any, any) { return A2{{true}, {false}}, [1]any{A2{}}[0] }

func main() {
	definedIntKinds()
	definedStringBool()
	definedFloat()
	structAndNil()
	errorResults()
	nonemptyInterfaceResult()
	instantiationBoxes()
	boxInBox()
	namedArrayDynamic()
}
