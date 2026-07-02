package main

func channelSelectFullSendDefault() int {
	ch := make(chan int, 1)
	ch <- 5
	picked := 0
	select {
	case ch <- 9:
		picked = 1
	default:
		picked = 2
	}
	return picked*100 + len(ch)*10 + <-ch
}
