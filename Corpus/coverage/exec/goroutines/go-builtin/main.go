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

func main() {
	goCloseBuiltin()
}
