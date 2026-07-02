package main

func main() {
	var ch <-chan int
	close(ch)
}
