package main

// E6ARANGE (the Stage E6a audit RE-VERIFICATION's R1, fix round 2, 2026-09-24): a `range`
// statement's key / value variables are the BODY's, never the enclosing block's — the positive
// controls for the scope-exact R1 declaration environment. Taken verbatim from the auditor's
// re-verification probe (docs/evidence/2026-09-24_unseq-stage-e6a-audit/reverify-p8-main.go,
// `qRangeLeakOuter` / `qRangeKeyLeakOuter`): fix round 1 pushed a range node's `keyVar` / `valVar`
// into the ENCLOSING environment (the `block` fold walked the range node and `nestedStmtKeys
// "range"` skipped only `body`), so with «innermost = last» a LEGAL program that shadows an outer
// variable of ANOTHER type with a range variable and graphs the OUTER one after the loop was
// REFUSED whole — a fail-closed WRONG REFUSAL against main and gc.
//
//	e6arange      — the value-variable spelling: outer `k` string, the range's `k` int; gc 23.
//	e6arangekey   — the key-variable spelling:   outer `i` string, the range's `i` int; gc 9.
//	e6arangeafter — the range variable is declared NOWHERE else, and a graph follows the loop;
//	                gc 8. It is the base of the mutant `mut-local-range-var-after-loop` (the
//	                auditor's h12): the final graph's `r` atom renamed to the range's `k`, RIGHT-
//	                typed — under the leak it decoded and stuck late («unbound GoCore variable
//	                address: k»), and it now refuses by name.
func wit(x int) int { println("wit", x); return x }

func e6arange() int {
	k := "ab"
	s := []int{7, 8}
	r := 0
	for _, k := range s {
		r += k
	}
	return s[len(k)-2] + wit(1) + r
}

func e6arangekey() int {
	i := "ab"
	s := []int{7, 8}
	r := 0
	for i := range s {
		r += i
	}
	return s[len(i)-2] + wit(1) + r
}

func e6arangeafter() int {
	s := []int{7}
	r := 0
	for _, k := range s {
		r += k
	}
	return s[r-7] + wit(1)
}

func main() { println(e6arange()); println(e6arangekey()); println(e6arangeafter()) }
