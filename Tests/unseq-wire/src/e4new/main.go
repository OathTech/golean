package main

// E4NEW (Stage E audit fix round F1, 2026-09-21): Go 1.26 `new(x)` inside an admitted sweep —
// `*new(m()) + x + h() + g()` with x captured by h (h: x = 2, returns 100; m prints `m` and
// returns 7; g prints `g` and returns 1). m, new, h and g are E1-ordered (new is a function
// call, spec#Built-in_functions); the fresh pointer's dereference follows new by data; x's read
// is spec-unsequenced against the calls — before h 7 + 1 + 100 + 1 = 109, after h 7 + 2 + 100 +
// 1 = 110, the output `m` then `g` on both. Reference enumerate.py E4g. The first E4 cut dropped
// the initializer and never ran m (the audit's f1-new-call-dropped-litmus: `g` 103); gc and main
// answer `m` `g` 110.
func m() int { println("m"); return 7 }
func g() int { println("g"); return 1 }

func e4new() int {
	x := 1
	h := func() int { x = 2; return 100 }
	return *new(m()) + x + h() + g()
}

func main() { println(e4new()) }
