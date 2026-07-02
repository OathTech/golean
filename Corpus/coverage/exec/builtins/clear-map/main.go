package main

func builtinClearMap() int {
	m := map[string]int{"a": 1, "b": 2}
	clear(m)
	score := 0
	if len(m) == 0 {
		score += 1
	}
	if _, ok := m["a"]; !ok {
		score += 10
	}
	m["c"] = 3
	return score + m["c"]
}

func main() {
	builtinClearMap()
}
