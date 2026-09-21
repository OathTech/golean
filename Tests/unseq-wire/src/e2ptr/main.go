package main

// E2PTR (Stage E, family E2 — pointers, fields, maps; lane core/unseq-stage-e-0921,
// 2026-09-21): `*p += mut()` with mut REDIRECTING the captured p from x to y. The
// target plan freezes the pointer VALUE (v2.1 §3.4): plan before mut → x = 11 (y 100);
// plan after → y = 101 (x 10); the hybrids (a load through one pointee, a store into
// the other) are not members. The reference is enumerate.py's E2e; the returned
// checksum x*1000 + y encodes the printed pair: {11100, 10101}.
func e2ptr() int {
	x, y := 10, 100
	p := &x
	mut := func() int { p = &y; return 1 }
	*p += mut()
	return x*1000 + y
}

func main() { println(e2ptr()) }
