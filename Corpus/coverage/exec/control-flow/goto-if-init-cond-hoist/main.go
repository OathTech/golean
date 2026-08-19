package main

// The one STRUCTURAL interaction of the BUG-058 fix (bug-fix arc slice
// 1, 2026-08-19): the fix makes an `if` with an init statement AND a
// hoisting condition emit as a wire `block` wrapping [init, hoists, if]
// instead of an `if` node carrying an `init` key. Inside a goto
// function that node sits at the top level of a restructured SEGMENT,
// where degradeGotoDeclares rewrites top-level source declarations into
// assignments to the pre-hoisted cells. The init's declaration is
// NESTED in both shapes (under the `init` key before, inside the block
// after), so it keeps its `declare` — which is correct, since a
// backward jump re-declares it — but "correct by the same argument in
// both shapes" is exactly the claim that deserves a case.

func dbl(v int) int { return v * 2 }

func gotoIfInitCondHoist() int {
	n := 0
	i := 0
loop:
	if x := i; dbl(x) < 6 {
		n = n*10 + x
		i++
		goto loop
	}
	return n
}
