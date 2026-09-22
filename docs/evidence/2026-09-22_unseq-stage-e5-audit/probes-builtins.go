package main

// Audit probes, Stage E5 family E5a (min/max/append/copy). [AGENT] auditor 2026-09-22.

func minArgVsCall() int { x := 1; m := func() int { x = 10; return 5 }; return min(x, m()) }    // {1, 5}
func callThenMin() int  { x := 1; m := func() int { x = 10; return 5 }; return m() + min(x, 100) } // {6, 15}
func maxFloatVsCall() float64 {
	f := 1.0
	m := func() float64 { f = 10; return 0.5 }
	return max(f, 2.5) + m()
}
func appendAliasRead() int { s := make([]int, 2, 4); s2 := s[:3]; return append(s, 3)[0] + s2[2] } // {0, 3}
func copyOverlapVsRead() int { s := []int{1, 2, 3, 4}; return copy(s[1:], s) + s[2] }               // {6, 5}
func capVsAppendCall() int {
	s := make([]int, 1, 1)
	m := func() int { s = append(s, 1); return 5 }
	return cap(s) + m() // 6 forced
}
func appendFullBase() int { s := []int{1, 2}; m := func() int { s[0] = 10; return 5 }; return append(s, 3)[0] + m() }
func minStringVsCall() string {
	s := "b"
	m := func() string { s = "a"; return "z" }
	return min(s, "c") + m() // "bz" forced
}
func appendResultPlanned() int {
	xs := make([][]int, 2)
	s := []int{1}
	f := func() int { s = append(s, 9); return 1 }
	xs[f()] = append(s, 2)
	return len(xs[1]) // {2, 3}
}
func realVsCall() float64 { c := complex(1, 2); m := func() float64 { return 0.5 }; return real(c) + m() }
func appendIfaceElemAddr() int {
	x := 1
	m := func() int { x = 10; return 5 }
	return len(append([]any{}, x, m())) // forced? x boxed inside append's window before m: 2
}

func callThenMinTwo() int { a, b := 1, 2; m := func() int { a = 10; b = 20; return 5 }; return m() + min(a, b) } // {6, 7, 15, 25}
