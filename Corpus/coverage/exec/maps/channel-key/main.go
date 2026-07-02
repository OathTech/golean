package main

func mapChannelKey() int {
	ch1 := make(chan int)
	ch2 := make(chan int)
	m := map[chan int]int{
		ch1: 3,
		ch2: 5,
	}
	return len(m)*100 + m[ch1]*10 + m[ch2]
}

func main() {
	mapChannelKey()
}
