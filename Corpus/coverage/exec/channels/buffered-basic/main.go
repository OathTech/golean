package main

func channelBufferedBasic() int {
	ch := make(chan int, 2)
	ch <- 3
	ch <- 4
	before := len(ch)*1000 + cap(ch)*100
	first := <-ch
	second := <-ch
	return before + first*10 + second
}

func main() {
	channelBufferedBasic()
}
