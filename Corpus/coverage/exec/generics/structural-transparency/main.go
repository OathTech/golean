package main

func stWrapSlice[T any](x T) any {
	return []T{x, x}
}

func stWrapMap[T any](k string, v T) any {
	return map[string]T{k: v}
}

func genericStructuralTransparency() int {
	score := 0
	if s, ok := stWrapSlice(4).([]int); ok {
		score += s[0] + s[1]
	}
	if _, ok := stWrapSlice(4).([]string); ok {
		score += 1000
	}
	if m, ok := stWrapMap("a", 7).(map[string]int); ok {
		score += 10 * m["a"]
	}
	return score
}

func main() {
	genericStructuralTransparency()
}
