package main

// Stage E5 of the evaluation-order model v2.1, family E5b (lane core/unseq-stage-e5-0922,
// 2026-09-22): MULTI-TARGET assignments — tuple assignment, blank targets, multi-value calls
// and the comma-ok forms. spec#Assignment_statements: «First, the operands of index expressions
// and pointer indirections … on the left and the expressions on the right are all evaluated in
// the usual order. Second, the assignments are carried out in left-to-right order.» In the graph
// every target is a PHASE-1 SIBLING plan (frozen operands; the plan checks nothing) and the
// stores ride phase 2 in order — the inventory's E3/E4 inter-target axis is the graph's own
// shape. References: enumerate.py E5b1–E5b4; the wires Tests/unseq-wire/{e5btuple,e5brecv2,
// e5bassert}.json + native-*.

func rebindS(ps *[]int) int { *ps = []int{7, 8, 9}; return 5 }
func two() (int, int)       { return 1, 5 }

// s[0], x = m(), 3 with s captured and m REBINDING it ([1, 2] → [7, 8, 9]; returns 5): the element
// target's plan freezes s's HEADER before or after m, so the store of 5 lands in the OLD array
// (old[0] = 5, s[0] = 7 → 57) or the NEW one (old[0] = 1, s[0] = 5 → 15). {57, 15}.
func tupleHeaderVsCall() int {
	s := []int{1, 2}
	old := s
	var x int
	m := func() int { return rebindS(&s) }
	s[0], x = m(), 3
	return old[0]*10 + s[0] + x - 3
}

// _, x = a[9], wit(1): the blank target's checked read (a = [1]) panics; wit is the sibling event —
// the panic alone, or `wit 1` then the panic. Membership on the output.
func blankPanicVsCall() int {
	a := []int{1}
	var x int
	_, x = a[9], wit(1)
	return x
}

func wit(x int) int { println("wit", x); return x }

// xs[a[9]], ok = <-ch (ch buffered, holding 3; a = [1]): the planned target's index read panics
// before the receive (the channel still holds 3) or after it (drained) — the deferred witness
// prints len(ch): {1, 0}.
func commaOkRecvTargetVsPanic() int {
	ch := make(chan int, 1)
	ch <- 3
	xs := []int{0}
	a := []int{1}
	var ok bool
	defer func() { println("len", len(ch)) }()
	xs[a[9]], ok = <-ch
	_ = ok
	return xs[0]
}

// x, s[0] = twoRebind(): the multi-value call REBINDS s ([1, 2] → [7, 8, 9]) and returns (1, 5);
// the element target's frozen header before or after the call: 57 or 15. {57, 15}.
func multiCallHeaderVsCall() int {
	s := []int{1, 2}
	old := s
	var x int
	twoRebind := func() (int, int) { s = []int{7, 8, 9}; return 1, 5 }
	x, s[0] = twoRebind()
	return old[0]*10 + s[0] + x - 1
}

// x, y := m(), s[0] — a DEFINE tuple with s captured and written by m (s[0] = 10; returns 5): the
// checked read of s[0] is spec-unsequenced against m — before m 5 + 1 = 6, after 5 + 10 = 15 (gc's).
// The declares ride the completion. {6, 15}.
func defineTupleVsCall() int {
	s := []int{1}
	m := func() int { s[0] = 10; return 5 }
	x, y := m(), s[0]
	return x + y
}

// STRICT CONTROL: a swap with no event stays legacy by name (no call occurrence): 21.
func swapControl() int {
	a, b := 1, 2
	a, b = b, a
	return a*10 + b
}

// STRICT CONTROL: a comma-ok map lookup alone (no event) stays legacy: v = 2, ok → 21.
func commaOkMapControl() int {
	m := map[int]int{1: 2}
	v, ok := m[1]
	if ok {
		return v*10 + 1
	}
	return 0
}

// --- the audit fix round (2026-09-22), F3: MAP-ELEMENT targets in a multi-target assignment ---

// m[k], y = 7, f() with k captured and f WRITING it (k = 2; returns 9): the map-element target is a
// PHASE-1 SIBLING plan on the frozen map value and the key's read — spec-unsequenced against f
// (spec#Assignment_statements phase 1, spec#Order_of_evaluation) — so the phase-2 store lands at
// the OLD key (m[1] = 7 → 709) or the NEW one (m[2] = 7 → 79, gc's: call-first). The LEGACY path
// QUARANTINES this shape («map element as assignment target outside a single assignment» —
// triage F6 / mini-slice A3, BUG-115); the graph path handles it: the store goes through the frozen
// `mapElem` plan in phase 2, no element address is ever taken. {709, 79}.
func mapTargetKeyVsWriter() int {
	m := map[int]int{}
	k := 1
	y := 0
	f := func() int { k = 2; return 9 }
	m[k], y = 7, f()
	return m[1]*100 + m[2]*10 + y
}

// xs[f()], ok = m[1] with m captured by f, which DELETES m[1] (returns 0): the comma-ok lookup is a
// RESIDUAL two-binder `wide` body (`WideSpec.mapLookup`, no E1 edge) unordered against f — before
// the delete (1, true): xs[0] = 1, ok → 11; after it (0, false) → 0 (gc's, call-first). The `wide
// map-lookup` arm's corpus control: audit F1 found the arm exercised by no row and no tracked wire.
// {11, 0}.
func commaOkMapTargetVsDelete() int {
	m := map[int]int{1: 1}
	xs := []int{0, 0}
	f := func() int { delete(m, 1); return 0 }
	var ok bool
	xs[f()], ok = m[1]
	if ok {
		return xs[0] + 10
	}
	return xs[0]
}

// THE QUARANTINE'S OWN ROW (red by design until mini-slice A3 lands — BUG-115): m[1], y = 1, wit(1)
// on a NIL map. Constant target operands and no non-event occurrence beside wit, so the RATIFIED
// trigger routes the sweep to the LEGACY path, which refuses the map-element target by name («map
// element as assignment target outside a single assignment»); gc runs it — `wit 1`, then
// «assignment to entry in nil map» (the store is phase 2, after the call). The SAME target shape
// with an observable operand (mapTargetKeyVsWriter above) runs on the GRAPH path: the
// trigger-dependent boundary the audit's F3 named.
func mapTargetNilLegacyRefusal() int {
	var m map[int]int
	y := 0
	m[1], y = 1, wit(1)
	return y
}
