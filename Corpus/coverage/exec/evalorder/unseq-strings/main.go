package main

// Stage E5 of the evaluation-order model v2.1, family E5e (lane core/unseq-stage-e5-0922,
// 2026-09-22): STRINGS. A string index `s[i]` is a bounds-checked byte read of an immutable
// value, a string slice `s[lo:hi]` a bounds-checked substring — FAILING PURE OPS on the string
// VALUE (spec#Index_expressions, spec#Slice_expressions), spec-unsequenced against the sibling
// calls; `len(s)` is an E1 participant like a slice's (spec#Length_and_capacity). References:
// enumerate.py E5e1/E5e2; the wire Tests/unseq-wire/e5estr.json + native.

// wit prints its argument and returns it (the effectful sibling of the panic rows).
func wit(n int) int {
	println("wit", n)
	return n
}

// int(s[i]) + m() with i captured (m: i = 1, returns 5): the byte read's bounds check and read before m
// yield 'a' (97 + 5 = 102), after m 'b' (98 + 5 = 103 — gc's: the plain byte read is deferred after
// the call, call-first). {102, 103}.
func strIndexVsCall() int {
	s := "ab"
	i := 0
	m := func() int { i = 1; return 5 }
	return int(s[i]) + m()
}

// int(s[i]) + wit(5) with i = 9 (a private local): the byte read PANICS (index out of range) either
// before wit (no output) or after it (`wit 5` printed first — gc's, call-first): the E13 sibling-panic
// shape on a string byte read. {panic · “, `wit 5` · panic}.
func strIndexPanicVsPrint() int {
	s := "ab"
	i := 9
	return int(s[i]) + wit(5)
}

// int(s[i:][0]) + m() with i captured (m: i = 1, returns 5): the substring s[i:] is a bounds-checked
// pure op on the string value and its byte [0] a second; both are spec-unsequenced against m —
// before m 'a' (97 + 5 = 102 — gc's: order.go hoists the string slice's temporary BEFORE the call, where
// the plain byte read s[i] of the row above is deferred after it), after m 'b' (98 + 5 = 103). {102, 103}. (`len(s[i:]) + m()`
// would be all-forced: the substring lies inside len's window and len precedes m — the strict
// control's shape.)
func strSliceVsCall() int {
	s := "ab"
	i := 0
	m := func() int { i = 1; return 5 }
	return int(s[i:][0]) + m()
}

// STRICT CONTROL: len(s) + m() with s captured (m: s = "xyz", returns 5): len is an E1 participant
// and s's read lies inside its window — forced before m: 2 + 5 = 7 on every stream (legacy by the
// trigger, every edge forced).
func strLenVsCall() int {
	s := "ab"
	m := func() int { s = "xyz"; return 5 }
	return len(s) + m()
}
