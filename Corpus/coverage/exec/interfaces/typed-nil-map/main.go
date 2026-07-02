package main

func typedNilMapInterface() int {
	var m map[string]int
	var x any = m
	score := 0
	if x != nil {
		score += 1
	}
	if x.(map[string]int) == nil {
		score += 10
	}
	return score + len(x.(map[string]int))*100
}

func main() {
	typedNilMapInterface()
}
