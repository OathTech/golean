package main

func channelSelectReadySend() int {
	ch := make(chan int, 1)
	picked := 0
	select {
	case ch <- 7:
		picked = 1
	default:
		picked = 2
	}
	return picked*100 + len(ch)*10 + <-ch
}
