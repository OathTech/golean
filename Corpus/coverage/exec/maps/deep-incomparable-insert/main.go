package main

// Map INSERTION with a deeply incomparable dynamic key: the key's
// dynamic type ([1]any) is statically comparable; the unhashable slice
// sits inside the boxed array's interface element. Insertion panics
// "hash of unhashable type []int" — the same value-directed hash walk
// maps/interface-key-nested-unhashable pins for struct/array boxes,
// here through the ARRAY-of-interface element on a STORE. Green cell
// from the external Codex review 2026-08-08
// (docs/2026-08-08_semantic-divergence-review.md §2).

func deepIncomparableInsert() int {
	m := map[any]int{}
	var k any = [1]any{[]int{1}}
	m[k] = 1
	return len(m)
}

func main() {
	deepIncomparableInsert()
}
