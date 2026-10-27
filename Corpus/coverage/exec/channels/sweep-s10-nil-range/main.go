package main

// Sweep lane sweep/s10-panics (2026-10-27), shape S10: the channel KINDS at
// two cells the channels/* rows do not pin — a range over a nil channel is a
// receive that blocks forever (gc: the deadlock FATAL, never a panic), and the
// close-of-closed panic is recoverable.

func rangeNilChanDeadlock() int {
	var c chan int
	n := 0
	for v := range c {
		n += v
	}
	return n
}

func closeClosedRecovered() int {
	c := make(chan int)
	close(c)
	r := 0
	func() {
		defer func() {
			if recover() != nil {
				r = 100
			}
		}()
		close(c)
	}()
	_, ok := <-c
	if !ok {
		r += 1
	}
	return r
}

func main() {}
