package main

import (
	"strings"
	"sub"
)

// Audit probes — Stage E6a attack 3: the unit boundary generalized.

func G(s []int, i int) int { s[i] = 5; return 1 }

func qualCallVsRead() int { // sub.Mut writes s[0]: the read s[0] before (1) or after (99) → {2, 100}
	s := []int{1}
	return sub.Mut(s) + s[0]
}

func qualGraphInSub() int { // the graph lives in sub.G
	s := []int{1}
	return sub.G(s, 9)
}

func methodOnSubPtr() int { // t.N through a pointer (nil-checked read) vs the mutating method call: {1, 2}
	t := &sub.T{}
	return t.Bump() + t.N
}

func valueRecvSub() int { // value receiver: the auto-deref of the pointer operand
	t := &sub.T{N: 3}
	return t.Val() + sub.Wit(5)
}

func libMethodVsIdx() int { // a stdlib source-through method callee (*strings.Reader).Len vs a failing read
	r := strings.NewReader("abc")
	s := []int{1}
	i := 9
	return r.Len() + s[i]
}

func libFuncVsIdx() int { // a stdlib source-through FUNCTION callee vs a failing read
	s := []int{1}
	i := 9
	return len(strings.TrimSpace(" a ")) + s[i]
}

func qualFuncVarRefused() int { // call through a qualified func-typed package variable: legacy by name
	s := []int{1}
	i := 9
	return sub.F(1) + s[i]
}

func genericSubRefused() int {
	s := []int{1}
	i := 9
	return sub.Id[int](3) + s[i]
}

func variadicSubRefused() int {
	s := []int{1}
	i := 9
	return sub.Sum(1, 2) + s[i]
}

func sameNameCollision() int { // main's G writes s[9]→panic; sub.H mutates s[0]
	s := []int{1}
	return sub.H(s) + G(s, 0) + s[0]
}

func subHGraph() int { // the graph inside sub.H: Mut(s) + s[0] → {2, 100}
	s := []int{1}
	return sub.H(s)
}

func main() {}
