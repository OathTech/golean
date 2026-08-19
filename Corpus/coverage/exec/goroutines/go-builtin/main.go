package main

// RED PIN (arc-final audit F22): `go` of a BUILT-IN call is legal Go
// (spec SGo statements: "Calls of built-in functions are restricted as
// for expression statements" — close/delete/panic/print/println/copy/
// clear are all legal in go position), and the arc's GoStmt lowering
// refuses the whole class fail-closed ("go of builtin <name>",
// emit.go). Correct direction, but the class had no corpus pin and no
// doc owner — this marker records it red until the lowering learns to
// wrap builtins in a synthesized thunk.

func goCloseBuiltin() int {
	ch := make(chan int, 1)
	ch <- 3
	done := make(chan int)
	go func() {
		<-ch // drains the buffered 3
		done <- 1
	}()
	go close(ch) // the refused shape: go of a builtin call
	<-done
	v, ok := <-ch // closed and empty after the drain: 0, false
	if ok {
		return -1
	}
	return v + 3
}

// Slice-6 enumeration (the whole-language bar, F15): the other legal
// builtin callees, one row per builtin the desugar must wrap. gc
// itself synthesizes a wrapper (`gowrap1` in the panic probe's
// traceback, artifacts/probe/slice6a — evidence FOR the thunk
// mechanism the F22 marker names). delete/copy observe COMPLETION
// only: `go delete(m,k)` offers no completion signal, so the child's
// effect is unobservable without a wrapper — the builtin's own effect
// suites carry effect correctness; these rows pin the CALLEE shape.

func goDeleteBuiltin() int {
	m := map[int]int{1: 1}
	go delete(m, 1)
	return 4
}

func goCopyBuiltin() int {
	dst := make([]int, 1)
	src := []int{5}
	go copy(dst, src)
	return 6
}

func goRecoverBuiltin() int {
	go recover() // never "directly by a deferred function": a no-op child
	return 7
}

func goPanicBuiltin() int {
	go panic("boom") // the child's unrecovered panic aborts the program
	<-make(chan int)
	return 0
}

func main() {
	goCloseBuiltin()
	goDeleteBuiltin()
	goCopyBuiltin()
	goRecoverBuiltin()
}
