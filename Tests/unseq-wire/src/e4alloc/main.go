package main

// E4ALLOC (Stage E, family E4 — conversions and allocations; lane core/unseq-stage-e-0921,
// 2026-09-21): BUG-102's slice-literal shape `[]int{s[i]}[0] + wit5()` — the payload read
// `s[i]` (out of range) is an occurrence spec-unsequenced against the call; the literal is an
// `allocate` body (a fresh backing array, NO E1 edge — v2.1 R3) on the payload's cell; the
// element read and the op follow by data. gc prints `wit 5` then panics; the machine also
// realizes the payload-first member. Reference enumerate.py E4b/E4c's shape;
// {panic [9] · ``, panic [9] · `wit 5`}. `i` is declared LAST so the hand-built wire keeps
// every setup statement through it (build.py's splice rule).
func wit5() int { println("wit", 5); return 5 }

func e4alloc() int {
	s := make([]int, 1)
	i := 9
	return []int{s[i]}[0] + wit5()
}

func main() { println(e4alloc()) }
