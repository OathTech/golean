package main

import "strings"

// S23 sweep — resource budgets (docs/defect-shapes.md; the plan
// docs/2026-10-27_defect-neighbourhood-campaign.md §4; lane sweep/s23-budgets,
// 2026-11-05): the string door. No budget bounds a string's length (the
// footprint budgets bound BACKINGS: make, append's spill, []byte(s)); the lane
// measured the model's string cost at about 16–20 bytes per byte (see
// BUG-410) and pins here the sizes that run — a 2^24-byte string by doubling
// with its reads, a 2^14-step concatenation loop, and a strings.Builder grown
// by doubling to 2^20 (its buffer is a byte backing: past 2^24 the spill
// refuses by name, measured by hand at 19.5 s and left off the corpus).
// gc answers on every row.

func doubleTo2p24() int {
	s := "ab"
	for i := 0; i < 23; i++ {
		s += s
	}
	t := s[1<<23 : 1<<23+3]
	eq := 0
	if s == s[:len(s)] {
		eq = 1
	}
	return len(s)*10 + int(s[len(s)-1]-'a') + len(t) + eq
}

func appendChar2p14() int {
	s := ""
	for i := 0; i < 1<<14; i++ {
		s += "x"
	}
	return len(s) + int(s[1<<14-1]-'x')
}

func builderInBudget() int {
	var sb strings.Builder
	sb.WriteString("x")
	for i := 0; i < 20; i++ {
		s := sb.String()
		sb.WriteString(s)
	}
	return sb.Len()
}

func main() {
	println(doubleTo2p24(), appendChar2p14(), builderInBudget())
}
