package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-012's line): built-in call arities the corpus did not hold — an
// append with no elements, min/max with one argument in a condition, len of
// an append, builtins as defer arguments, and builtins inside a generic
// body. Expected = gc go1.26.5.

var calls int

func take(x int) { calls += x }

func lenG[T any](s []T, v T) int {
	s = append(s, v)
	t := make([]T, len(s), len(s)+1)
	n := copy(t, s)
	return len(t)*100 + cap(t)*10 + n
}

// B11.2
func appendNoElems() int {
	s := []int{1, 2}
	t := append(s)
	t = append(t, 3)
	return len(s)*10 + len(t) // 23
}

// B11.16
func minOneArgCond() int {
	x := 4
	r := 0
	if min(x) == 4 && max(x) == x {
		r = 1
	}
	return r*10 + min(x) // 14
}

func lenOfAppend() int {
	s := []int{1}
	return len(append(s, 2, 3))*10 + len(append([]int(nil), 1)) // 31 (cap is the appendSpill envelope, S18 — not observed here)
}

// B11.14
func builtinDeferArgs() int {
	calls = 0
	s := []int{1, 2, 3}
	m := map[int]int{1: 1}
	func() {
		defer take(len(s))
		defer take(cap(s) * 10)
		defer take(len(m) * 100)
		defer take(min(len(s), 2) * 1000)
		s = nil
	}()
	return calls // 3 + 30 + 100 + 2000 = 2133
}

func builtinInGeneric() int {
	return lenG([]int{1, 2}, 3) + lenG([]string{}, "a") // 3*100 + 4*10 + 3 = 343; 1*100 + 2*10 + 1 = 121 → 464
}

func main() {
	println(appendNoElems(), minOneArgCond(), lenOfAppend(), builtinDeferArgs(), builtinInGeneric())
}
