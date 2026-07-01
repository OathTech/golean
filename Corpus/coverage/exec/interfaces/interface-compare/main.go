package main

func interfaceCompare() int {
	var a any = 1
	var b any = "1"
	var c any = 1
	var d any = 1
	score := 0
	if a == b {
		score += 1
	}
	if c == d {
		score += 10
	}
	return score
}
