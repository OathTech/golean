package main

// Re-verification probes (fix round 28919dd6), F3: map-element targets in multi-target assignments. [AGENT] auditor.

func wit(n int) int { println("wit", n); return n }

// the key OPERAND panics in phase 1 — unordered against wit (spec#Assignment_statements phase 1)
func mapTargetKeyPanicVsCall() int {
	m := map[int]int{}
	a := []int{1}
	y := 0
	m[a[9]], y = 1, wit(1)
	return y // {panic·``, `wit 1`·panic}
}
// the right-hand call DELETES the target's key: the store is phase 2, after f — m[1] = 7 regardless
func mapTargetRhsDeletesKey() int {
	m := map[int]int{1: 5}
	f := func() int { delete(m, 1); return 9 }
	y := 0
	m[1], y = 7, f()
	return m[1]*100 + len(m)*10 + y // 719 singleton
}
// the right-hand call REWRITES the target's key: phase 2 wins — m[1] = 7
func mapTargetRhsRewritesKey() int {
	m := map[int]int{1: 5}
	f := func() int { m[1] = 42; return 9 }
	y := 0
	m[1], y = 7, f()
	return m[1]*100 + y // 709 singleton
}
// the right-hand call REBINDS the captured map: the frozen map VALUE before / after f
func mapTargetRhsRebindsMap() int {
	m := map[int]int{1: 5}
	old := m
	f := func() int { m = map[int]int{}; return 9 }
	y := 0
	m[1], y = 7, f()
	return len(old)*100 + len(m)*10 + y // {119 (old gets the store: old=1,new=0 → 100+0+9=109)...}
}
// two map-element targets with a call on the right that writes the read key
func mapTwoTargetsVsCall() int {
	m := map[int]int{0: 1, 1: 2}
	f := func() int { m[0] = 9; return 5 }
	m[0], m[1] = f(), m[0]
	return m[0]*10 + m[1] // {51, 59}
}
// the comma-ok lookup vs a REWRITING call
func commaOkMapTargetVsRewrite() int {
	m := map[int]int{1: 1}
	xs := []int{0, 0}
	f := func() int { m[1] = 5; return 0 }
	var ok bool
	xs[f()], ok = m[1]
	if ok {
		return xs[0] + 10
	}
	return xs[0] // {11, 15}
}
// a PRIVATE (never captured) EMPTY map as the comma-ok base — the source-local annotation path of the F1 check
func commaOkPrivateEmptyMap() int {
	m := map[int]int{}
	xs := []int{0, 0}
	f := func() int { return 0 }
	var ok bool
	xs[f()], ok = m[1]
	if ok {
		return 1
	}
	return xs[0] + 100 // 100 (forced)
}
// a PRIVATE map as a multi-target map-element target
func mapTargetPrivateVsCall() int {
	m := map[int]int{}
	k := 1
	y := 0
	f := func() int { k = 2; return 9 }
	m[k], y = 7, f()
	return m[1]*100 + m[2]*10 + y // {709, 79}
}

// an ADMITTED sweep whose wide-lookup base is a PRIVATE (source-local atom) EMPTY map: the key read a[0] is the observable
func commaOkPrivateMapKeyRead() int {
	m := map[int]int{}
	a := []int{1}
	xs := []int{0, 0}
	f := func() int { a[0] = 2; return 0 }
	var ok bool
	xs[f()], ok = m[a[0]]
	if ok {
		return 1
	}
	return xs[0] + 100 // 100 (m empty either way)
}
