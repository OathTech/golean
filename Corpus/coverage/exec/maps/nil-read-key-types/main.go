package main

type nilReadKey struct {
	x int
}

func mapNilReadKeyTypes() int {
	var arrays map[[2]int]int
	var structs map[nilReadKey]int
	var chans map[chan int]int
	ch := make(chan int)
	score := 0
	if _, ok := arrays[[2]int{1, 2}]; !ok {
		score += 1
	}
	if _, ok := structs[nilReadKey{x: 3}]; !ok {
		score += 10
	}
	if _, ok := chans[ch]; !ok {
		score += 100
	}
	return score
}

func main() {
	mapNilReadKeyTypes()
}
