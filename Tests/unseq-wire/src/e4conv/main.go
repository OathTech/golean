package main

// E4CONV (Stage E, family E4): `int([]byte(s)[0]) + mut()` with s CAPTURED (mut: s = "zz",
// returns 1) — the conversion `[]byte(s)` is a pure head over s's value and the checked `[0]` a
// pure op on the fresh bytes; the READ of s is the occurrence spec-unsequenced against mut
// (E12's value axis): before mut 'a' + 1 = 98, after 'z' + 1 = 123. Reference enumerate.py
// E4a; {98, 123}. E12's recorded exception (`bytes-conv-value-vs-mutating-call`, gc 98) is
// the same shape.
func e4conv() int {
	s := "ab"
	mut := func() int { s = "zz"; return 1 }
	return int([]byte(s)[0]) + mut()
}

func main() { println(e4conv()) }
