package main

func bad() {
	var recvOnly <-chan int = make(chan int)
	var sendOnly chan<- int = recvOnly
	_ = sendOnly
}
