package main

func channelSelectNilDefault() int {
	var ch chan int
	select {
	case <-ch:
		return 1
	default:
		return 2
	}
}

func main() {
	channelSelectNilDefault()
}
