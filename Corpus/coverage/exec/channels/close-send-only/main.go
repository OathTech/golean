package main

func closeSendOnly(ch chan<- int) {
	close(ch)
}

func channelCloseSendOnly() int {
	ch := make(chan int, 1)
	ch <- 6
	closeSendOnly(ch)
	v, ok := <-ch
	score := v * 10
	if ok {
		score++
	}
	return score
}
