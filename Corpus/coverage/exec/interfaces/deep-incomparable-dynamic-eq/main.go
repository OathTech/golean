package main

// Deep interface-comparability panic through DYNAMIC types: two `any`
// values whose dynamic type ([1]any) is statically comparable, with the
// incomparable value (a slice) one interface level down inside the
// array element. Go's == recurses into the boxed array's interface
// element and panics "comparing uncomparable type []int". Complements
// interfaces/interface-array-compare-panic (STATIC array operands).
// Green cell from the external Codex review 2026-08-08
// (docs/2026-08-08_semantic-divergence-review.md §2).

func deepIncomparableDynamicEq() int {
	var x any = [1]any{[]int{1}}
	var y any = [1]any{[]int{1}}
	if x == y {
		return 1
	}
	return 0
}

func main() {
	deepIncomparableDynamicEq()
}
