package main

// E4MAKE (Stage E audit fix round F3, 2026-09-21): a `make-slice` allocation inside an admitted
// sweep — `len(make([]int, n)) + x + h()` with x captured by h (h: x = 10, returns 100) and n
// private (2): make is an E1-ordered call, len after it, h after len; x's read is unordered
// against h → {2 + 1 + 100, 2 + 10 + 100} = {103, 112}; gc 112 (call-first). The base wire for
// the constant-size mutants (a negative constant length; a constant len over a constant cap).
func e4make() int {
	n := 2
	x := 1
	h := func() int { x = 10; return 100 }
	return len(make([]int, n)) + x + h()
}

func main() { println(e4make()) }
