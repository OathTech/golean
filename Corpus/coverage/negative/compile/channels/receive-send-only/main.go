package main

func main() {
	var ch chan<- int
	_ = <-ch
}
