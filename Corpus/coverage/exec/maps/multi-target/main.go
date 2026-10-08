package main

// maps/multi-target — BUG-115 / triage F6 / mini-slice A3 (lane fix/bug115-map-multiassign-1008,
// 2026-10-08): a MAP ELEMENT as an assignment target outside the single-assignment fast path —
// tuple forms, multi-value calls, the comma-ok forms, select delivery, parenthesized spellings.
// spec#Assignment_statements: «First, the operands of index expressions and pointer indirections
// … on the left and the expressions on the right are all evaluated in the usual order. Second,
// the assignments are carried out in left-to-right order.» The target lowers to the machine's
// map-element PLAN (`Assignee.mapElem`, the E2 frozen plan): the map VALUE and the key VALUE are
// phase-1 operands, the store is phase 2 through `mapAssignValue` — a nil map panics AT THE
// STORE, after every phase-1 call and operand panic, left to right among the sibling stores.
// Every row is strict: constant target operands keep the sweeps on the LEGACY path (no non-event
// occurrence beside the calls), so these rows pin the legacy lowering — the trigger-admitted
// shape is evalorder/unseq-multi/map-target-key-vs-writer (membership, unchanged by the fix).
// Red-first: before the fix every subject but the parenthesized compound/increment spellings was
// refused by name («map element as assignment target outside a single assignment»); the
// parenthesized spellings lowered to an `index-addr` on the MAP VALUE (the quarantine's own
// hazard, missed through the parentheses) and are pinned here too.

func wit(x int) int   { println("wit", x); return x }
func boom() int       { panic("boom") }
func two() (int, int) { return 1, 5 }

// m[1], y = 7, wit(9): the call runs in phase 1, the stores land in phase 2 — 79.
func rhsCallEffect() int {
	m := map[int]int{}
	y := 0
	m[1], y = 7, wit(9)
	return m[1]*10 + y
}

// m[1], y = 7, boom(): the right-hand call panics in phase 1, so NO store happens — the deferred
// witness prints `len 0`, then the panic propagates: `len 0` · panic boom.
func rhsCallPanics() int {
	m := map[int]int{}
	y := 0
	defer func() { println("len", len(m)) }()
	m[1], y = 7, boom()
	return m[1]*10 + y
}

// var m map[int]int; m[1], y = 7, boom(): the phase-1 call's panic wins over the phase-2 nil-map
// store, which never runs: panic boom, not «assignment to entry in nil map».
func nilMapVsRhsPanic() int {
	var m map[int]int
	y := 0
	m[1], y = 7, boom()
	return y
}

// y, m[1] = wit(1), 7 on a nil map: the call first (phase 1), then the plain store, then the map
// store panics (phase 2, left to right): `wit 1` · panic «assignment to entry in nil map».
func nilMapSecondTarget() int {
	var m map[int]int
	y := 0
	y, m[1] = wit(1), 7
	return y
}

// m[1], s[0] = s[0], m[1]: a swap across a map element and a slice element — both right-hand
// values are read in phase 1, before either store: m[1] = 3, s[0] = 2 → 32.
func mapAndSliceSwap() int {
	m := map[int]int{1: 2}
	s := []int{3}
	m[1], s[0] = s[0], m[1]
	return m[1]*10 + s[0]
}

// m[1], s[9] = 1, 2 with m nil and len(s) = 1: phase 2 stores left to right, so the nil-map
// store panics FIRST; the slice store's bounds check never fires: «assignment to entry in nil map».
func nilMapThenSliceOob() int {
	var m map[int]int
	s := []int{0}
	m[1], s[9] = 1, 2
	return s[0]
}

// s[9], m[1] = 1, 2 with len(s) = 1 and m nil: the slice store is first — its bounds check
// panics before the nil-map store: «index out of range [9] with length 1».
func sliceOobThenNilMap() int {
	var m map[int]int
	s := []int{0}
	s[9], m[1] = 1, 2
	return s[0]
}

// m[1], m2[a[9]] = 1, 2 with m nil and len(a) = 1: the SECOND target's key operand a[9] is
// phase-1 material and panics before ANY phase-2 store — the first target's nil-map store never
// runs: «index out of range [9] with length 1», not «assignment to entry in nil map».
func keyPanicBeforeNilStore() int {
	var m map[int]int
	m2 := map[int]int{}
	a := []int{0}
	m[1], m2[a[9]] = 1, 2
	return len(m2)
}

// m[1], y = two(): the multi-value call's components store left to right — 15.
func multiValueCall() int {
	m := map[int]int{}
	y := 0
	m[1], y = two()
	return m[1]*10 + y
}

// m[wit(1)], y = wit(2), 3: a call inside the target's key precedes the right-hand call
// (spec#Order_of_evaluation, lexical order) — `wit 1` · `wit 2`; m[1] = 2, y = 3 → 23.
func targetCallOrder() int {
	m := map[int]int{}
	y := 0
	m[wit(1)], y = wit(2), 3
	return m[1]*10 + y
}

// m[1], ok = x.(int): the comma-ok type assertion with a map-element value target — 51.
func commaOkAssertMapTarget() int {
	m := map[int]int{}
	var x any = 5
	var ok bool
	m[1], ok = x.(int)
	if ok {
		return m[1]*10 + 1
	}
	return m[1] * 10
}

// m[1], ok = m2[5]: the comma-ok map lookup with a map-element value target — 71.
func commaOkLookupMapTarget() int {
	m := map[int]int{}
	m2 := map[int]int{5: 7}
	var ok bool
	m[1], ok = m2[5]
	if ok {
		return m[1]*10 + 1
	}
	return m[1] * 10
}

// mi[1], y = 5, 6 with mi map[int]any: the right-hand value boxes at the element type before the
// raw store — 56.
func interfaceElemTuple() int {
	mi := map[int]any{}
	y := 0
	mi[1], y = 5, 6
	return mi[1].(int)*10 + y
}

// select { case m[wit(1)] = <-ch: }: the receive clause's map-element target with a call in its
// key (spec#Select_statements step 4: the left-hand side evaluates after the communication) —
// the clause's write-back carries the map plan: `wit 1`; m[1] = 7 → 7.
func selectRecvMapTarget() int {
	m := map[int]int{}
	ch := make(chan int, 1)
	ch <- 7
	select {
	case m[wit(1)] = <-ch:
	}
	return m[1]
}

// select { case mi[1] = <-ch: } with mi map[int]any: the received int boxes at the element type
// in the clause's write-back — 7.
func selectRecvMapIfaceElem() int {
	mi := map[int]any{}
	ch := make(chan int, 1)
	ch <- 7
	select {
	case mi[1] = <-ch:
	}
	return mi[1].(int)
}

// (m[1]), y = 4, 2: a parenthesized map-element target is the same non-addressable element — 42.
func parenTupleTarget() int {
	m := map[int]int{}
	y := 0
	(m[1]), y = 4, 2
	return m[1]*10 + y
}

// (m[1]) = 4: the parenthesized single-target spelling — 4.
func parenSingleTarget() int {
	m := map[int]int{}
	(m[1]) = 4
	return m[1]
}

// (m[1]) += 4: the parenthesized compound spelling (read-then-store) — 5.
func parenCompound() int {
	m := map[int]int{1: 1}
	(m[1]) += 4
	return m[1]
}

// (m[1])++: the parenthesized increment spelling — 2.
func parenIncDec() int {
	m := map[int]int{1: 1}
	(m[1])++
	return m[1]
}
