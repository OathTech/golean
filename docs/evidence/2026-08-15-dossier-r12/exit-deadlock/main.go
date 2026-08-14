package main

func main() {
	var ch chan int
	<-ch // nil channel: blocks forever; gc's detector fires
}
