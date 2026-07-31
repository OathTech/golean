package main

// The array-element half of the value-directed hash walk (pre-merge audit
// 2026-07-31, finding 1): `[2]any` is a comparable key TYPE whose elements may
// hold unhashable dynamic values.

func arrayKeyAssign() int {
	m := map[[2]any]int{}
	m[[2]any{1, []int{1}}] = 1
	return len(m)
}

func arrayKeyAccessEmpty() int {
	m := map[[2]any]int{}
	return m[[2]any{1, []int{1}}]
}
