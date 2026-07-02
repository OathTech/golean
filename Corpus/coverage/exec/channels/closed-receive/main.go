package main

func channelClosedReceive() int {
	ch := make(chan int, 1)
	ch <- 7
	close(ch)
	first, okFirst := <-ch
	second, okSecond := <-ch
	score := first*10 + second
	if okFirst {
		score += 1000
	}
	if !okSecond {
		score += 100
	}
	return score
}

func main() {
	channelClosedReceive()
}
