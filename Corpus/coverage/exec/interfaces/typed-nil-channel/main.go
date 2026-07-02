package main

func typedNilChannelInterface() int {
	var ch chan int
	var x any = ch
	score := 0
	if x != nil {
		score += 1
	}
	if x.(chan int) == nil {
		score += 10
	}
	return score + len(x.(chan int))*100
}

func main() {
	typedNilChannelInterface()
}
