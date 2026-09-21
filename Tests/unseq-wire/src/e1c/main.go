package main

// E1C (Stage E, family E1): g += f() with g a PACKAGE-LEVEL variable and f
// writing it (g = 10, returns 1). The compound target's load is the READ
// occurrence of g, unsequenced against f; the store rides `then` through the
// operand-free identity `addr(globaladdr)`: read before f → g = 1 + 1 = 2
// (overwriting f's 10), read after f → 10 + 1 = 11 (gc's, call-first). {2, 11}.
// The reference is enumerate.py's E1c.
var g = 1

func f() int { g = 10; return 1 }

func e1c() int {
	g += f()
	return g
}

func main() { println(e1c()) }
