package main

// Compile-only aggregator: spec decl-fragment blocks whose entire content is
// "this form is legal" with no observable behavior. Each group is commented
// with its spec anchor + block id; the single subject returns a constant —
// the case's value is that the frontend must ACCEPT these forms.

// ---- spec#Function_types block Function_types-2-90bee491: the function
// type forms. Tfn stands in for the block's T (a type is required).
type Tfn struct{}

var (
	_ func()
	_ func(x int) int
	_ func(a, _ int, z float32) bool
	_ func(a, b int, z float32) bool
	_ func(prefix string, values ...int)
	_ func(a, b int, z float64, opt ...interface{}) (success bool)
	_ func(int, int, float64) (float64, *[]int)
	_ func(n int) func(p *Tfn)
)

// ---- spec#Satisfying_a_type_constraint block
// Satisfying_a_type_constraint-1-1c69f8c6, the SATISFIED rows (the
// not-satisfied rows are negative-case material, out of this aggregator's
// positive lane):
//
//	int implements interface{ ~int }
//	string implements comparable (strictly comparable)
//	any satisfies (but does not implement) comparable [Go 1.20]
//	struct{f any} satisfies comparable
//	interface{ m() } implements interface{ comparable; m() }
func satTildeInt[P interface{ ~int }]() {}
func satComparable[P comparable]()      {}

type mIface interface{ m() }

func satComparableM[P interface {
	comparable
	m()
}]() {
}

var (
	_ = satTildeInt[int]
	_ = satComparable[string]
	_ = satComparable[any]
	_ = satComparable[struct{ f any }]
	_ = satComparableM[mIface]
)

// ---- spec#Instantiations block Instantiations-1-1a7fd952, the legal rows:
//
//	[P any] with int; [S ~[]E, E any] with []int, int; [P comparable] with
//	any (satisfies without implementing). The io.Writer row is illegal by
//	design and the illegal half is out of this aggregator's positive lane.
func instAny[P any](x P)           {}
func instSlice[S ~[]E, E any](s S) {}

var (
	_ = instAny[int]
	_ = instSlice[[]int, int]
	_ = satComparable[any] // [P comparable] instantiated with any
)

// ---- spec#Errors block Errors-1-cf107147: the predeclared error interface,
// re-declared at package level — legal, and SHADOWS the universe's error
// inside this package.
type error interface {
	Error() string
}

// ---- spec#Errors block Errors-2-011342e6: the error-last signature
// convention. File is a stand-in and a body is added (the spec shows only
// the signature).
type File struct{}

func Read(f *File, b []byte) (n int, err error) { return 0, nil }

func compileOnlyForms() int {
	return 1
}
