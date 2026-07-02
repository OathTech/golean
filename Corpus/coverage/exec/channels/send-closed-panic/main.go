package main

func channelSendClosedPanic() {
	ch := make(chan int, 1)
	close(ch)
	ch <- 1
}

func main() {
	channelSendClosedPanic()
}
