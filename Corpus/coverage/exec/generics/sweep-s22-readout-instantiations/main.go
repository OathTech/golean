package main

// Sweep lane sweep/s22-readout (2026-11-07), shape S22 — the readout (the matrix is on the member entries'
// Neighbourhood lines in docs/BUGS.md, BUG-013 above all; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group A9: reflect.Type.Name() of an instantiation is `Tag[<args>]` with the arguments in the runtime's spelling —
// package-qualified named types, `*`, `[]`, `[N]`, `map[K]V`, `func(…)`, `error`, `,`-joined parameters.

type T struct{ X int }
type K8 int8
type S string
type Tag[A any] struct{ N int }
type Two[A, B any] struct{ N int }
type Box[A any] struct{ V A }

func mk[A any](v A) Box[A] { return Box[A]{v} }

func pointerArg() (Tag[*T], any, Tag[**T]) {
	return Tag[*T]{1}, Tag[*T]{2}, Tag[**T]{3}
}
func sliceAndArrayArgs() (Tag[[]int], any, Tag[[2]string], any) {
	return Tag[[]int]{1}, Tag[[]T]{2}, Tag[[2]string]{3}, Tag[[0]K8]{4}
}
func mapArgs() (Tag[map[string]int], any, any) {
	return Tag[map[string]int]{1}, Tag[map[K8][]T]{2}, Tag[map[string]map[int]bool]{3}
}
func funcArg() (Tag[func()], any, any) {
	return Tag[func()]{1}, Tag[func(int, string) (int, error)]{2}, Tag[func(...int) bool]{3}
}
func errorArg() (Tag[error], any) { return Tag[error]{1}, Tag[error]{2} }
func definedKindArgs() (Tag[K8], any, Tag[S]) {
	return Tag[K8]{1}, Tag[K8]{2}, Tag[S]{3}
}
func twoParams() (Two[int, string], any, any) {
	return Two[int, string]{1}, Two[K8, *T]{2}, Two[Tag[int], []S]{3}
}
func pointerToInstantiation() (Tag[*Tag[int]], any) {
	return Tag[*Tag[int]]{1}, Tag[*Box[*T]]{2}
}
func genericFunctionResult() (Box[int], Box[S], any) {
	return mk(1), mk(S("s")), mk(T{4})
}

func main() {
	pointerArg()
	sliceAndArrayArgs()
	mapArgs()
	funcArg()
	errorArg()
	definedKindArgs()
	twoParams()
	pointerToInstantiation()
	genericFunctionResult()
}
