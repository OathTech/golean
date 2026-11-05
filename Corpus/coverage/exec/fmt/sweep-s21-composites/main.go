package main

// Sweep lane sweep/s21-stdlib (2026-11-05), shape S21 — stdlib shims and source-through
// (the matrix is on the member entries' Neighbourhood lines in docs/BUGS.md, BUG-089/086/073/071/154/153;
// the plan is docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group A10: %v / %+v over composites (fmtcomposite.go fmtRenderValue / fmtSliceLift) at the leaf kinds and depths the v-composites rows omit.
import "fmt"

type empty struct{}
type kk int32
type allInts struct {
	A int8
	B int16
	C int32
	D int64
	E uint8
	F uint16
	G uint32
	H uint64
	I uint
	J int
	K uintptr
}
type leaf struct{ X int }
type holder struct{ A []leaf }
type l3 struct{ B l2 }
type l2 struct{ C l1 }
type l1 struct{ D int }
type bs struct {
	B bool
	S string
}
type ns struct{ S []int }
type sl2 struct{ T [][]string }
type nbool bool
type withNamedBool struct {
	A int
	B nbool
}

func emptyStruct() string    { return fmt.Sprintf("%v|%+v", empty{}, empty{}) }
func sliceNamedInts() string { return fmt.Sprintf("%v|%v", []kk{1, -2}, []kk{}) }
func structAllIntKinds() string {
	return fmt.Sprintf("%v|%+v", allInts{-1, -2, -3, -4, 5, 6, 7, 8, 9, 10, 11}, allInts{K: 1})
}
func sliceOfSlices() string { return fmt.Sprintf("%v", [][]int{{1, 2}, {}, nil}) }
func structWithSliceOfStructs() string {
	return fmt.Sprintf("%v|%+v", holder{[]leaf{{1}, {2}}}, holder{nil})
}
func plusVDepth3() string           { return fmt.Sprintf("%+v|%v", l3{l2{l1{7}}}, l3{}) }
func boolAndStringFields() string   { return fmt.Sprintf("%v|%+v", bs{true, "s t"}, bs{}) }
func nilSliceField() string         { return fmt.Sprintf("%v|%+v", ns{}, ns{[]int{}}) }
func sliceOfSliceOfStrings() string { return fmt.Sprintf("%v", sl2{[][]string{{"a", "b c"}, {}}}) }
func namedBoolField() string        { return fmt.Sprintf("%v|%+v", withNamedBool{1, true}, withNamedBool{}) }

func main() {
	emptyStruct()
	sliceNamedInts()
	structAllIntKinds()
	sliceOfSlices()
	structWithSliceOfStructs()
	plusVDepth3()
	boolAndStringFields()
	nilSliceField()
	sliceOfSliceOfStrings()
	namedBoolField()
}
