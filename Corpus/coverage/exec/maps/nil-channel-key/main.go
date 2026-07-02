package main

func mapNilChannelKey() int {
	var ch chan int
	other := make(chan int)
	m := map[chan int]int{ch: 7}
	return len(m)*100 + m[ch]*10 + m[other]
}

func main() {
	mapNilChannelKey()
}
