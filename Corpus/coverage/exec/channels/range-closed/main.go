package main

func channelRangeClosed() int {
	ch := make(chan int, 3)
	ch <- 2
	ch <- 4
	ch <- 6
	close(ch)
	sum := 0
	count := 0
	for x := range ch {
		sum += x
		count++
	}
	return count*100 + sum
}

func main() {
	channelRangeClosed()
}
