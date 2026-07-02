package main

func typedNilCompositeInterface() int {
	var p *int
	var s []int
	var m map[string]int
	xs := []any{p, s, m}
	score := 0
	if xs[0] != nil {
		score += 1
	}
	if xs[1] != nil {
		score += 10
	}
	if xs[2] != nil {
		score += 100
	}
	if v := xs[0].(*int); v == nil {
		score += 1000
	}
	if v := xs[1].([]int); v == nil {
		score += 10000
	}
	if v := xs[2].(map[string]int); v == nil {
		score += 100000
	}
	return score
}

func main() {
	typedNilCompositeInterface()
}
