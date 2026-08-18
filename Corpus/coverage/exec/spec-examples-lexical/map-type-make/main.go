// spec#Map_types block Map_types-3-e7a32402
// The spec's two make-a-map forms: make(map[string]int) and
// make(map[string]int, 100). Pins that both start empty (the capacity
// hint does not affect length), and that inserted elements are
// retrievable — the hint is only a hint.
package main

func mapMakeForms() int {
	m1 := make(map[string]int)
	m2 := make(map[string]int, 100)
	score := 0
	if len(m1) == 0 {
		score += 1
	}
	if len(m2) == 0 {
		score += 2
	}
	m1["a"] = 1
	m2["b"] = 2
	m2["c"] = 3
	if len(m1) == 1 {
		score += 4
	}
	if len(m2) == 2 {
		score += 8
	}
	if m1["a"]+m2["b"]+m2["c"] == 6 {
		score += 16
	}
	return score
}

func main() {
	mapMakeForms()
}
