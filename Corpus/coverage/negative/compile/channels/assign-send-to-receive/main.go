package main

func bad() {
	var sendOnly chan<- int = make(chan int)
	var recvOnly <-chan int = sendOnly
	_ = recvOnly
}
