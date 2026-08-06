package main

// Range-over-channel corners beyond the basic closed-drain (range-closed):
// break leaves the remaining buffer in place, and the variable-free form
// iterates by receive count.

func channelRangeBreak() int {
	ch := make(chan int, 3)
	ch <- 1
	ch <- 2
	ch <- 3
	close(ch)
	sum := 0
	for v := range ch {
		sum += v
		if v == 2 {
			break
		}
	}
	return sum*10 + len(ch)
}

func channelRangeNoVar() int {
	ch := make(chan int, 2)
	ch <- 7
	ch <- 8
	close(ch)
	count := 0
	for range ch {
		count++
	}
	return count*10 + len(ch)
}

func main() {
	channelRangeBreak()
}
