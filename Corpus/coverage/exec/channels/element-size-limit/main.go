package main

// gc's channel element limit (cmd/compile/internal/types/size.go
// TCHANARGS: an element width >= 1<<16 is rejected): these are the
// largest ACCEPTED elements — one byte, and one int, below 64 KiB. The
// rejected neighbours (chan [65536]byte, chan [8192]int) are negative
// rows (Corpus/coverage/negative/compile/channels/chan-elem-*).

func channelElemMaxBytes() int {
	c := make(chan [65535]byte, 1)
	var a [65535]byte
	a[0] = 3
	a[65534] = 4
	c <- a
	b := <-c
	return int(b[0])*10 + int(b[65534])
}

func channelElemMaxInts() int {
	var c chan [8191]int
	if c == nil {
		return 1
	}
	return 0
}

func main() {
	channelElemMaxBytes()
	channelElemMaxInts()
}
