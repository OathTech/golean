package main

func builtinMakeChannelLenCap() int {
	ch := make(chan int, 2)
	ch <- 7
	return len(ch)*10 + cap(ch)
}

func main() {
	builtinMakeChannelLenCap()
}
