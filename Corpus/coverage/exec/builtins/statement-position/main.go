// Built-in calls in EXPRESSION-STATEMENT position (spec#Expression_statements:
// "With the exception of specific built-in functions, function and method
// calls and receive operations can appear in statement context"; the
// not-permitted list is append/cap/complex/imag/len/make/new/real/unsafe.*,
// so `copy` and `recover` ARE permitted there and their result is simply
// discarded).
//
// Landed guardrails-first by the bug-fix arc's triage slice (slice 5,
// mini-slice A1): before the fix the frontend refused ANY other builtin in
// statement position ("builtin %s in statement position"), which quarantined
// the whole declaration — a visible red, but a refusal of ordinary Go.
// `copy` in statement position occurs in etcd-io/raft (util.go,
// tracker/inflights.go), so this is a north-star shape.
//
// Every expectation below was computed from `go run` BEFORE the fix
// (artifacts/probe/triage-stmtbuiltin, scratch): 450, 11234, 12450, 105050,
// 5, 4, 7 in the order declared.
package main

func stmtMark(trace *int, tag int, xs []int) []int { *trace = *trace*10 + tag; return xs }

// The count is discarded; the destination writes still happen.
func stmtCopy() int {
	dst := []int{0, 0, 0}
	src := []int{4, 5}
	copy(dst, src)
	return dst[0]*100 + dst[1]*10 + dst[2]
}

// spec#Appending_and_copying_slices: "The source and destination may overlap."
// Statement position must not lose the as-if-intermediate semantics.
func stmtCopyOverlap() int {
	xs := []int{1, 2, 3, 4, 5}
	copy(xs[1:], xs[:4])
	return xs[0]*10000 + xs[1]*1000 + xs[2]*100 + xs[3]*10 + xs[4]
}

// Discarding the result must not discard the operands' evaluation order:
// dst is evaluated before src (trace 12), as in expression position.
func stmtCopyEvalOrder() int {
	trace := 0
	dst := []int{0, 0, 0}
	src := []int{4, 5}
	copy(stmtMark(&trace, 1, dst), stmtMark(&trace, 2, src))
	return trace*1000 + dst[0]*100 + dst[1]*10 + dst[2]
}

// The string-source form takes a different arm than the slice-source one.
func stmtCopyStringToBytes() int {
	dst := []byte{0, 0, 0}
	copy(dst, "hi")
	return int(dst[0])*1000 + int(dst[1])*10 + int(dst[2])
}

// spec#Handling_panics: a bare `recover()` STATEMENT is still "called
// directly by a deferred function", so it stops the panicking sequence even
// though its result is discarded.
func stmtRecoverInDefer() (r int) {
	defer func() {
		recover()
		r = 5
	}()
	panic("boom")
}

// No panic in flight: recover returns nil and the deferred function runs on.
func stmtRecoverNoPanic() (r int) {
	defer func() {
		recover()
		r = r + 1
	}()
	return 3
}

// Not called by a deferred function: a no-op that must not swallow anything.
func stmtRecoverOutsideDefer() int {
	recover()
	return 7
}
