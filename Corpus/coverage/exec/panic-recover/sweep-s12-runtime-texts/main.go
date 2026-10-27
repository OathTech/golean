package main

// Sweep S12 — run-time error TEXTS at the abort line (matrix cells D02,
// D04–D06, D10–D14; lane sweep/s12-panic-recover, 2026-10-27). Whether the
// panic is RAISED is the sibling shape S10's; here the first abort line is
// compared against gc's text (runtime/error.go boundsError.Error, the
// plainError texts of chan.go / map.go / slice.go / alg.go). The machine:
// `indexOutOfRangePanic`, `checkSliceBounds3` / `checkSliceMax` (Ops.lean),
// the chan / map / make / hash / compare arms. Bounds come in as ARGUMENTS
// so gc cannot fold them at compile time.

func rtNegativeIndex(i int) int {
	s := []int{1}
	return s[i]
}

func rtArray3Index(n int) int {
	var a [3]int
	s := a[0:1:n]
	return len(s)
}

func rtSlice3Index(n int) int {
	s := make([]int, 2, 4)
	t := s[0:1:n]
	return len(t)
}

func rtSlice3IndexLowHigh(lo int, hi int) int {
	s := make([]int, 2, 4)
	t := s[lo:hi:4]
	return len(t)
}

func rtNilMapWrite() {
	var m map[string]int
	m["a"] = 1
}

func rtCloseNil() {
	var c chan int
	close(c)
}

func rtCloseClosed() {
	c := make(chan int)
	close(c)
	close(c)
}

func rtMakesliceLen(n int) int {
	s := make([]int, n)
	return len(s)
}

func rtMakesliceCap(n int, c int) int {
	s := make([]int, n, c)
	return cap(s)
}

func rtMakechan(n int) int {
	c := make(chan int, n)
	return cap(c)
}

func rtUnhashable() int {
	m := map[any]int{}
	m[[]int{1}] = 1
	return len(m)
}

func rtUncomparable() bool {
	var a any = []int{1}
	var b any = []int{1}
	return a == b
}

func main() {}
