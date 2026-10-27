package main

// Sweep S19, lane sweep/s19-init-order, 2026-10-27 (cell B7): an `init`
// function is a real frame — an early `return` exits that init only, and
// the next init in source order still runs.

var tr int

func mark(x int) int { tr = tr*10 + x; return x }

func init() {
	mark(1)
	if tr > 0 {
		return
	}
	mark(9)
}

func init() { mark(2) }

func initEarlyReturn() int { return tr }

func main() { println(initEarlyReturn()) }
