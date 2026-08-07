package main

// Buffered wake: a sender parks on a FULL buffer and resumes when the
// receiver makes room. FIFO must survive the blocked-sender window
// (probe p18's shape, across goroutines): single sender + single
// receiver ⇒ values received in the order sent (spec §Channel types).

func bufferedWakeFIFO() int {
	ch := make(chan int, 2)
	done := make(chan int)
	go func() {
		for i := 1; i <= 5; i++ {
			ch <- i // sends 3.. park until main drains
		}
		done <- 1
	}()
	acc := 0
	for i := 0; i < 5; i++ {
		acc = acc*10 + <-ch
	}
	<-done
	return acc
}

// cap=1 alternation: every second send parks; the drain order is still
// 1,2,3.
func bufferedWakeCapOne() int {
	ch := make(chan int, 1)
	done := make(chan int)
	go func() {
		ch <- 1
		ch <- 2
		ch <- 3
		close(ch)
		done <- 1
	}()
	acc := 0
	for v := range ch {
		acc = acc*10 + v
	}
	<-done
	return acc
}


// len/cap observed at SYNC points only (confluent): after the join the
// buffer state is schedule-independent. Closes the audit-noted gap
// (zero len/cap uses across goroutines cases); the schedule-DEPENDENT
// occupancy observations live in sched-dependent/ (membership).
func bufferedLenAfterJoin() int {
	ch := make(chan int, 3)
	done := make(chan int)
	go func() {
		ch <- 1
		ch <- 2
		done <- 1
	}()
	<-done
	// both sends completed-before the done rendezvous: len is pinned
	return len(ch)*100 + cap(ch)*10 + <-ch
}

func main() {
	bufferedWakeFIFO()
	bufferedWakeCapOne()
	bufferedLenAfterJoin()
}
