package main

func main() {
	var ch <-chan int
	ch <- 1
}
