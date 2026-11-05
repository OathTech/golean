// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). A PARENTHESISED multi-value call
// in a multi-value context — `a, b := (pair())`, `var c, d = (pair())`, `return (pair())`,
// `add((pair()))` — legal Go (go/types reads the tuple through the parentheses), gc runs
// it — BUG-422 (born red): the emitter's multi-value call tests read the operand without
// ast.Unparen, so the spelling falls to the single-value hoist and is refused by name as a
// tuple hoisted as a single value, while the unparenthesised spelling lowers;
// expected = gc go1.26.5.

package main

func pair() (int, int) { return 3, 4 }

func add(a, b int) int { return a + b }

func retParenMulti() (int, int) { return (pair()) }

func parenMultiValueDefine() int {
	a, b := (pair())
	return a + b*10 // 43
}

func parenMultiValueVar() int {
	var c, d = (pair())
	return c + d*10 // 43
}

func parenMultiValueAssign() int {
	var c, d int
	c, d = (pair())
	return c + d*10 // 43
}

func parenMultiValueReturn() int {
	e, f := retParenMulti()
	return e + f*10 // 43
}

func parenMultiValueSpread() int {
	return add((pair())) // 7
}

func main() {
	println("parenMultiValueDefine", parenMultiValueDefine())
	println("parenMultiValueVar", parenMultiValueVar())
	println("parenMultiValueAssign", parenMultiValueAssign())
	println("parenMultiValueReturn", parenMultiValueReturn())
	println("parenMultiValueSpread", parenMultiValueSpread())
}
