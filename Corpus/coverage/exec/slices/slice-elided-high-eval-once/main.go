package main

// BUG-066 guardrails: a slice expression with an ELIDED high bound must
// evaluate its base exactly once. The frontend's default-high lowering
// (`len(base)`) re-emitted the base, so a call-valued base ran TWICE —
// gc 1 call, machine 2, status ok (census 2026-08-21 §10 H-a).

func callBase() int {
	calls := 0
	expensive := func() []int {
		calls++
		return []int{10, 20, 30}
	}
	s := expensive()[:]
	return calls*100 + len(s)*10 + s[2]%10
}

func callBaseLowOnly() int {
	calls := 0
	expensive := func() []int {
		calls++
		return []int{10, 20, 30}
	}
	s := expensive()[1:]
	return calls*100 + len(s)*10 + s[0]%10
}

func explicitHighControl() int {
	calls := 0
	expensive := func() []int {
		calls++
		return []int{10, 20, 30}
	}
	s := expensive()[0:3]
	return calls*100 + len(s)*10 + s[2]%10
}

// The four BASE-SHAPE classes the fix also corrected but nothing pinned
// (holes-arc audit fix round 2026-08-21, finding F2). Each was a live
// re-evaluation of the base with an elided high; the counters below are
// the gc-derived expectations (go1.26.5), and the pre-fix machine values
// are recorded beside them so a regression is legible as the OLD number,
// not just "not green".

// Nested slice expression: the inner `f()[1:]` is itself the outer's
// base, so the pre-fix lowering re-emitted it at BOTH levels and `f` ran
// FOUR times. gc 133, pre-fix machine 433.
func nestedSliceExpr() int {
	c := 0
	f := func() []int {
		c++
		return []int{1, 2, 3, 4, 5}
	}
	s := f()[1:][1:]
	return c*100 + len(s)*10 + s[0]
}

// Map-index base with an EFFECTFUL KEY: the key expression is inside the
// re-emitted base, so the key call ran twice (and, with a mutating key,
// could have selected a different entry for the length than for the
// value). gc 122, pre-fix machine 222.
func mapIndexEffectfulKey() int {
	c := 0
	m := map[int][]int{5: {1, 2, 3}}
	k := func() int {
		c++
		return 5
	}
	s := m[k()][1:]
	return c*100 + len(s)*10 + s[0]
}

// Pointer-to-array call base, `pf()[1:]` — the POINTER-REUSE path (no
// explicit deref, no field selector): the operand is the pointer itself
// and its static array length is the default high. gc 128, pre-fix
// machine 228.
func pointerArrayCallBase() int {
	c := 0
	arr := [3]int{7, 8, 9}
	pf := func() *[3]int {
		c++
		return &arr
	}
	s := pf()[1:]
	return c*100 + len(s)*10 + s[0]%10
}

// CONVERSION base: `[]byte(f())[1:]` — the conversion (and the call
// inside it) sat in the re-emitted operand, so the string was built
// twice. gc 131, pre-fix machine 231. Closest relative: BUG-047's
// conversion eval-once guard, which covered the conversion's own operand
// but not a conversion used AS a slice base.
func conversionBase() int {
	c := 0
	f := func() string {
		c++
		return "wxyz"
	}
	s := []byte(f())[1:]
	return c*100 + len(s)*10 + int(s[0]-'w')
}
