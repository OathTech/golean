// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// The parenthesised builtin spelling (len)(fs()) / (cap)(fs()) — BUG-287 (born red): the
// emitter takes the parenthesised builtin for a func-typed callee expression and exports a
// call through a func value named len/cap, which the decoder refuses with a cause that
// misnames itself (a source local 'len' not in scope). gc evaluates fs() once: 103.

package main

var cnt int

func fs() []int { cnt++; return []int{10, 20, 30} }

func parenBuiltin() int {
	cnt = 0
	n := (len)(fs())
	return cnt*100 + n
}

func parenBuiltinCap() int {
	cnt = 0
	n := (cap)(fs())
	return cnt*100 + n
}

func main() {
	parenBuiltin()
	parenBuiltinCap()
}
