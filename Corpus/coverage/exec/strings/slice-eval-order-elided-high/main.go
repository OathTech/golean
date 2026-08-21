package main

// BUG-066 guardrail: `strings/slice-eval-order`'s elided-high sibling. The
// explicit-high row was the census's near miss — it pins base-then-low-then-
// high order but never elides high, which is exactly where the base was
// emitted twice (census 2026-08-21 §10 H-a).

func stringSliceEvalOrderElidedHigh() int {
	log := 0
	source := func() string {
		log = log*10 + 1
		return "abcd"
	}
	lo := func() int {
		log = log*10 + 2
		return 1
	}
	s := source()[lo():]
	return log*100 + len(s)*10 + int(s[0])
}
