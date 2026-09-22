package main

// Audit probes, Stage E5 family E5e (strings). [AGENT] auditor 2026-09-22.

func wit(n int) int { println("wit", n); return n }

func strReassignVsIndex() int { s := "ab"; m := func() int { s = "zz"; return 5 }; return int(s[0]) + m() } // {102, 127}
func strIndexStatusDiverse() int {
	s := "ab"
	i := 0
	m := func() int { i = 9; return 5 }
	return int(s[i]) + m() // {102, panic}
}
func strSliceOOBVsPrint() int { s := "ab"; i := 9; return int(s[i:][0]) + wit(5) } // {panic, `wit 5` panic}
func strConcatIndexVsCall() int { s := "a"; m := func() int { s = "b"; return 5 }; return int((s + "x")[0]) + m() } // {102, 103}
func strSliceReassign() string {
	s := "abc"
	m := func() string { s = "xyz"; return "!" }
	return s[1:] + m() // {"bc!", "yz!"}
}
func strLenSliceForced() int { s := "abc"; i := 1; m := func() int { i = 2; return 5 }; return len(s[i:]) + m() } // 7
func strIndexVsReassignBoth() int {
	s := "ab"
	i := 0
	m := func() int { s = "xyz"; i = 2; return 5 }
	return int(s[i]) + m() // {102, 127, 125, panic}
}
func strFullSliceRefused() string { s := "abc"; m := func() string { s = "x"; return "!" }; b := []byte(s); return string(b[0:1:2]) + m() }
