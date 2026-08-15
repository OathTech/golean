package main

// E3 guardrails (gallery campaign G2, 2026-08-15): calls in
// short-circuit operands, the risk classes pinned BEFORE the
// normalization lands (fidelity argument:
// docs/gallery-campaign-log/g2.md, "E3 — THE FIDELITY ARGUMENT").
// Every subject encodes the helper-evaluation record into its
// returned value, so the go-run oracle detects:
//   - double evaluation (the count/trace grows),
//   - eager right-operand evaluation (the count/trace grows when the
//     left operand already decided),
//   - order swap (the trace digits permute),
//   - per-iteration re-evaluation of a short-circuit loop guard.
// Until the normalization lands these rows are RED at stage
// frontend-export with the standing quarantine reason
// ("call/allocation in short-circuit operand (would change
// evaluation order)") — visible expected gaps, per guardrails-first.

// evals counts helper evaluations; trace digit-encodes their order.
var evals uint64
var trace uint64

func isPos(x uint64) bool {
	evals++
	return x > 0
}

func mark(k uint64, v bool) bool {
	trace = trace*10 + k
	return v
}

// scCount: `&&` in an if condition. Returns result*100 + evals: an
// eagerly evaluated right operand (or a double evaluation) changes
// the count even when the result is unchanged.
func scCount(a, b uint64) uint64 {
	evals = 0
	r := uint64(0)
	if isPos(a) && isPos(b) {
		r = 1
	}
	return r*100 + evals
}

// scOrder: `||` order witness. Returns trace*10 + result: digits pin
// left-to-right order and exactly-when-needed evaluation.
func scOrder(a, b uint64) uint64 {
	trace = 0
	r := uint64(0)
	if mark(1, a > 0) || mark(2, b > 0) {
		r = 1
	}
	return trace*10 + r
}

// scNested: f(a) && (g(b) || h(c)) — the nested normalization; the
// inner machinery must sit inside the outer conditional body.
func scNested(a, b, c uint64) uint64 {
	trace = 0
	r := uint64(0)
	if mark(1, a > 0) && (mark(2, b > 0) || mark(3, c > 0)) {
		r = 1
	}
	return trace*10 + r
}

// scLoop: a short-circuit loop guard re-evaluates BOTH operands (the
// right one exactly-when-needed) on every iteration — the stein shape
// isolated. Returns iterations*100 + evals.
func scLoop(a, b uint64) uint64 {
	evals = 0
	n := uint64(0)
	for isPos(a) && isPos(b) {
		a--
		b -= 2
		n++
	}
	return n*100 + evals
}

// scAssign: the short-circuit result consumed from a plain
// assignment (expression position, not a condition).
func scAssign(a, b uint64) uint64 {
	evals = 0
	ok := isPos(a) && isPos(b)
	r := uint64(0)
	if ok {
		r = 1
	}
	return r*100 + evals
}

func main() {
	scCount(1, 2)
	scOrder(0, 1)
	scNested(1, 0, 1)
	scLoop(3, 6)
	scAssign(1, 0)
}
