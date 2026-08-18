// spec#Channel_types block Channel_types-2-04dbba2f
// The spec's three channel-type forms: chan T (send and receive),
// chan<- float64 (send-only), <-chan int (receive-only). A
// bidirectional channel assigns to each directional type; values sent
// through the restricted views round-trip, pinning that the direction
// restriction is a TYPE property, not a different channel.
package main

type T int

func channelDirectionForms() int {
	bidi := make(chan T, 1) // chan T: can send and receive values of type T
	cf := make(chan float64, 1)
	ci := make(chan int, 1)
	var send chan<- float64 = cf // can only be used to send float64s
	var recv <-chan int = ci     // can only be used to receive ints
	score := 0
	bidi <- T(7)
	if got := <-bidi; int(got) == 7 {
		score += 1
	}
	send <- 0.5
	if f := <-cf; f == 0.5 {
		score += 2
	}
	ci <- 42
	if n := <-recv; n == 42 {
		score += 4
	}
	return score
}

func main() {
	channelDirectionForms()
}
