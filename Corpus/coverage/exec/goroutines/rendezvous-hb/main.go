package main

// The channel happens-before edges as OBSERVABLE ordering (memory
// model §Channel communication): channel-synchronized shared-memory
// access is DRF and deterministic.

var shared int

// "A send on a channel is synchronized before the completion of the
// corresponding receive": the worker's write is visible after main's
// receive.
func rendezvousSendHB() int {
	done := make(chan int)
	go func() {
		shared = 41
		done <- 1
	}()
	<-done
	return shared + 1
}

// "A receive from an unbuffered channel is synchronized before the
// completion of the corresponding send" (go_mem's hello-world shape):
// the worker writes, then RECEIVES; main's SEND completes only after,
// so main's read sees the write.
func rendezvousRecvHB() int {
	c := make(chan int)
	go func() {
		shared = 33
		<-c
	}()
	c <- 0
	return shared
}

func main() {
	rendezvousSendHB()
	rendezvousRecvHB()
}
