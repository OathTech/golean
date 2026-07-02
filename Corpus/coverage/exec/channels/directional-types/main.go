package main

func sendDirectional(ch chan<- int, v int) {
	ch <- v
}

func receiveDirectional(ch <-chan int) int {
	return <-ch
}

func channelDirectionalTypes() int {
	ch := make(chan int, 2)
	var sendOnly chan<- int = ch
	var recvOnly <-chan int = ch
	sendOnly <- 3
	sendDirectional(sendOnly, 4)
	return receiveDirectional(recvOnly)*10 + <-recvOnly
}
