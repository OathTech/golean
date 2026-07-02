package main

func channelMakeDirectional() int {
	recvOnly := make(<-chan int, 2)
	sendOnly := make(chan<- int, 3)
	return len(recvOnly)*1000 + cap(recvOnly)*100 + len(sendOnly)*10 + cap(sendOnly)
}
