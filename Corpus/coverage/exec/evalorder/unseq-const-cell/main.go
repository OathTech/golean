package main

// A CONSTANT copied into a cell inside a native `unseq` graph (evaluation-order
// model v2.1 Stage C, lane core/unseq-stage-c-0919; the adversarial audit
// docs/2026-09-20_unseq-stage-c-audit.md F2, programs a14/a15/a16 verbatim):
// the pilot grammar admits a constant operand (design
// docs/2026-09-19_unseq-stage-c-design.md §1), and the lowering copies it into a
// CELL where the consumer needs one — a guard's test (`true && f()`) or a
// phase-2 store's value (`a[f()] = 5`, `a[f()] = "s"`; design §6 «the value must
// be a CELL: a constant or atom value is copied into one»). The decoder's D8 as
// first landed at C1 listed no constant head and REFUSED the frontend's own
// emission — a fail-closed coverage REGRESSION on legal Go that ran on main
// (main's legacy ANF lowers all three). Red-first: each row was born
// FAIL/lean-observation on the candidate (the named refusal «head 'bool'|'int'|
// 'string' … is outside the Stage C fragment») and PASSES since D8 admits
// constant heads typed by the wire's annotation (D9 still refuses a constant
// whose type disagrees with its cell). Every sweep here is all-forced (the
// call is the only event, the constant an atom): strict singletons, the same
// observation main's binary gives.

// a14: `ok := true && f()` — a constant guard test copied into a bool cell;
// f (in the region) sets the captured a. ok → 2; main 2.
func constGuardLeft() int {
	a := 1
	f := func() bool { a = 2; return true }
	ok := true && f()
	if ok {
		return a
	}
	return -1
}

// a15: `a[f()] = 5` — an int constant copied into the store's value cell;
// f prints, writes a[1] = 9, returns 0 → a = [5, 9] → 59; main `f` · 59.
func elemAssignConstInt() int {
	a := []int{1, 2}
	f := func() int { println("f"); a[1] = 9; return 0 }
	a[f()] = 5
	return a[0]*10 + a[1]
}

// a16: `a[f()] = "s"` — a string constant copied into the store's value cell;
// f prints, returns 1 → a = ["x", "s"] → "xs"; main `f` · "xs".
func elemAssignConstString() string {
	a := []string{"x", "y"}
	f := func() int { println("f"); return 1 }
	a[f()] = "s"
	return a[0] + a[1]
}

func main() {
	println(constGuardLeft())
	println(elemAssignConstInt())
	println(elemAssignConstString())
}
