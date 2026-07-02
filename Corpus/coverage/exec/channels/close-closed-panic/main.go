package main

func channelCloseClosedPanic() {
	ch := make(chan int)
	close(ch)
	close(ch)
}

func main() {
	channelCloseClosedPanic()
}
