package main

type comparableStruct struct {
	x int
	y string
}

func structComparable() int {
	a := comparableStruct{x: 1, y: "go"}
	b := comparableStruct{x: 1, y: "go"}
	c := comparableStruct{x: 2, y: "go"}
	score := 0
	if a == b {
		score += 1
	}
	if a != c {
		score += 10
	}
	return score
}

func main() {
	structComparable()
}
