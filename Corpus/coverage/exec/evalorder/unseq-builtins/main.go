package main

// Stage E5 of the evaluation-order model v2.1, family E5a (lane core/unseq-stage-e5-0922,
// 2026-09-22): the reading-(a) BUILT-INS. RATIFIED [USER] 2026-09-22 (relayed): the built-ins
// are the «function calls» of spec#Order_of_evaluation's ordering sentence
// (spec#Built-in_functions «called like any other function»), so `min`/`max`/`copy`/`append`
// are E1 participants — ordered lexically among the calls, their operands evaluated inside
// their windows (forced before every later participant), never unordered reads. `min`/`max`
// have no effect (pure heads); `append` and `copy` are EFFECTFUL (the append's in-place element
// store when capacity allows, the copy's destination write), so a sibling read is observable
// against them — the trigger admits the sweep. References: enumerate.py E5a1–E5a7; the wires
// Tests/unseq-wire/{e5append,e5copy,e5minmax}.json + native-*. gc's draws are call-first
// (order.go's call class holds OMIN/OMAX/OCOPY/OAPPEND).

// STRICT CONTROL (reading (a)): min(x, 100) + m() with m writing the captured x (1 → 10, returns
// 5): min is E1-ordered BEFORE m and x's read lies inside min's window — forced before m: 1 + 5
// = 6 on every stream (the audit's probe k1's shape; legacy by the trigger, every edge forced).
func minVsCall() int {
	x := 1
	m := func() int { x = 10; return 5 }
	return min(x, 100) + m()
}

// min inside an admitted graph: min(x, 100) + y + m() with y captured (m: y = 10, returns 5): min
// first (E1), the read of y spec-unsequenced against m — before m 1 + 1 + 5 = 7, after 1 + 10 + 5
// = 16 (gc's). {7, 16}.
func minMaxReadVsCall() int {
	x := 1
	y := 1
	m := func() int { y = 10; return 5 }
	return min(x, 100) + y + m()
}

// append(s, 3)[0] + m(): s = make([]int, 2, 4) holding [1, 2] — capacity for the in-place append;
// m writes s[0] = 10 and returns 5. append is E1-ordered before m and stores 3 IN PLACE (the result
// aliases s's array); the result's [0] read is spec-unsequenced against m — before m 1 + 5 = 6,
// after 10 + 5 = 15 (gc's, call-first). {6, 15}.
func appendReadVsCall() int {
	s := make([]int, 2, 4)
	s[0], s[1] = 1, 2
	m := func() int { s[0] = 10; return 5 }
	return append(s, 3)[0] + m()
}

// d[0] + copy(d, s): d = [0, 0], s = [7, 8]. copy is an EFFECTFUL E1 participant (it writes d);
// the sibling checked read d[0] is spec-unsequenced against it — before the copy 0 + 2 = 2, after
// 7 + 2 = 9 (gc's: OCOPY is in order.go's call class, the copy first). {2, 9}.
func copyEffectVsRead() int {
	d := []int{0, 0}
	s := []int{7, 8}
	return d[0] + copy(d, s)
}

// append(b, "xy"...) — a spread STRING operand (the pure bytes-from-string head inside append's
// window); len after the append (E1), m after len; x captured (m: x = 10): {3 + 1 + 5, 3 + 10 + 5}
// = {9, 18}, gc 18. b has CAPACITY for the append (make([]byte, 1, 8)) so no `appendSpill`
// capacity pick joins the sweep — the ONE consumption site stays the scheduler's (a full base
// spills and adds the capacity site at bound 30, which the row's width would have to cover).
func appendSpreadStrVsCall() int {
	b := make([]byte, 1, 8)
	b[0] = 'a'
	x := 1
	m := func() int { x = 10; return 5 }
	return len(append(b, "xy"...)) + x + m()
}

// STRICT: copy as a STATEMENT — copy(d, f()) with f returning the source and writing d[1] = 4:
// the copy's operands are inside its window; the captured d's HEADER read is unordered against
// f (which writes an element, never the header) — one pick, one observation; the count is
// discarded: d = [7, 8] after the copy (f's write precedes the copy's), 78.
func copyStmtControl() int {
	d := []int{0, 0}
	f := func() []int { d[1] = 4; return []int{7, 8} }
	copy(d, f())
	return d[0]*10 + d[1]
}
