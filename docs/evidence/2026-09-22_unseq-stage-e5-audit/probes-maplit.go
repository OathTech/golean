package main

// Audit probes, Stage E5 family E5c (map literals). [AGENT] auditor 2026-09-22.

func mapLitCallsInside() int {
	k := func() int { println("k"); return 1 }
	v := func() int { println("v"); return 2 }
	m := func() int { println("m"); return 5 }
	return map[int]int{k(): v()}[1] + m() // k v m; 7
}
// spec#Order_of_evaluation's own example: `map[int]int{a: 1, a: 2}` may be {2: 1} or {2: 2} — the entry STORE order is
// unspecified. The machine (legacy and E5c's mapLit arm) stores entries in source order → the last wins only.
func mapLitDupDynamic() int { k1, k2 := 1, 1; m := func() int { return 5 }; return map[int]int{k1: 1, k2: 2}[1] + m() } // machine 7; spec also 6
func mapLitDupDynamicSpec() int {
	a := 1
	f := func() int { a++; return a }
	f()
	mm := map[int]int{a: 1, a: 2}
	return mm[2]*10 + len(mm) // spec: 11 or 21
}
func mapLitIfaceValue() int { x := 1; m := func() int { x = 10; return 5 }; return map[int]any{1: x}[1].(int) + m() } // {6, 15}
func mapLitStringKeyVsCall() int { s := "a"; m := func() int { s = "b"; return 5 }; return map[string]int{s: 1}["a"] + m() } // {6, 5}
func mapLitAsCommaOkBase() int {
	x := 1
	f := func() int { x = 2; return 1 }
	var ok bool
	xs := []int{0, 0}
	xs[f()], ok = map[int]int{x: 7}[1]
	if ok {
		return xs[1]
	}
	return -1
}
func mapLitValueCallVsKeyRead() int {
	a := []int{1}
	f := func() int { a[0] = 9; return 5 }
	mm := map[int]int{a[0]: f()}
	return mm[1]*10 + mm[9] // {50, 5}
}

func mapLitNestedValue() int { x := 1; m := func() int { x = 10; return 5 }; return map[int][]int{1: {x}}[1][0] + m() } // {6, 15}
