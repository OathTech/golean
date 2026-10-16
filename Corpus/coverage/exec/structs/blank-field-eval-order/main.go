package main

// RED BY DESIGN since the 2026-10-14 ruling ([USER] Mike, both halves agreed,
// BUG-129): a CALL at a blank field is not a constant, nil or a plain
// variable read, so the literal refuses by name (FAIL/frontend-export,
// by-design/blank-field-operand). Born 2026-10-13 as PASS rows pinning the
// call's evaluation and output order on both lowering paths; gc's answers
// stand in the rows (the calls run, in order).

type blankOrderS struct {
	_ int
	X int
	_ int
}

type blankOrderT struct {
	_ any
	X int
}

func blankOrderWitness(v int) int {
	println("wit", v)
	return v
}

// Closure calls on the legacy ANF path.
func blankOrderEffectful() int {
	state := 0
	mark := func(v int) int {
		state = state*10 + v
		println("mark", v)
		return v
	}
	s := blankOrderS{mark(1), mark(2), mark(3)}
	return state*10 + s.X
}

// An interface-typed blank boxing an effectful operand.
func blankOrderBoxedEffectful() int {
	state := 0
	mark := func(v int) int {
		state = state*10 + v
		println("mark", v)
		return v
	}
	t := blankOrderT{mark(1), mark(2)}
	return state*10 + t.X
}

// Top-level calls beside a checked slice access: the unseq sweep path.
func blankOrderSweep() int {
	xs := []int{10, 20, 30}
	i := 1
	s := blankOrderS{blankOrderWitness(1), xs[i], blankOrderWitness(2)}
	return s.X
}
