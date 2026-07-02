package main

func channelCloseNilPanic() {
	var ch chan int
	close(ch)
}

func main() {
	channelCloseNilPanic()
}
