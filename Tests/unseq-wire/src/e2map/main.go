package main

// E2MAP (Stage E, family E2): `m[1] += mut()` with mut REBINDING the captured m to m2.
// The target plan freezes the map VALUE (a reference) and the key: plan before mut →
// the OLD map's entry becomes 11 (m2's stays 100); plan after → m2's entry becomes 101
// (the old one stays 10); no hybrid. The reference is enumerate.py's E2f (the spike's
// R4, on a map); the checksum old[1]*1000 + m[1]: {11100, 10101}.
func e2map() int {
	m := map[int]int{1: 10}
	m2 := map[int]int{1: 100}
	old := m
	mut := func() int { m = m2; return 1 }
	m[1] += mut()
	return old[1]*1000 + m[1]
}

func main() { println(e2map()) }
