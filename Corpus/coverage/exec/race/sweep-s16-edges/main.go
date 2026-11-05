package main

// S16 sweep, family EDGES (the defect-neighbourhood campaign, lane sweep/s16-race,
// 2026-10-27; matrix §A21, §E): the happens-before edges the detector must have —
// and must not have — beside the channel-object keys.

type pairE struct{ a, b int }

func (p pairE) send(c chan int) { c <- p.a }

// A21: `go o.send(done)` copies the value receiver at the go statement,
// before the edge; the parent's later field write is ordered after the copy.
func edgesGoValueRecvCopiedAtSpawn() int {
	o := pairE{a: 1}
	done := make(chan int)
	go o.send(done)
	o.b = 2
	y := <-done
	return y*10 + o.b
}

// E2: the unbuffered edge in the WRONG direction — the receiver writes after
// its receive, the sender reads after its send.
func edgesUnbufferedWrongDirection() int {
	x := 0
	ch := make(chan int)
	done := make(chan int)
	go func() {
		<-ch
		x = 1
		done <- 0
	}()
	ch <- 0
	y := x
	<-done
	return y + x
}

// E3: capacity 1 — the 2nd send completes after the 1st receive (k/k+C).
func edgesBufCap1SecondSendEdge() int {
	x := 0
	ch := make(chan int, 1)
	done := make(chan int)
	go func() {
		x = 1
		<-ch
		<-ch
		done <- 0
	}()
	ch <- 0
	ch <- 0
	y := x
	<-done
	return y
}

// E4: capacity 1 — a read after the 1st send only.
func edgesBufCap1FirstSendNoEdge() int {
	x := 0
	ch := make(chan int, 1)
	done := make(chan int)
	go func() {
		x = 1
		<-ch
		<-ch
		done <- 0
	}()
	ch <- 0
	y := x
	ch <- 0
	<-done
	return y + x
}

// E5: capacity 2 — the 3rd send completes after the 1st receive.
func edgesBufCap2ThirdSendEdge() int {
	x := 0
	ch := make(chan int, 2)
	done := make(chan int)
	go func() {
		x = 1
		<-ch
		<-ch
		<-ch
		done <- 0
	}()
	ch <- 0
	ch <- 0
	ch <- 0
	y := x
	<-done
	return y
}

// E6: capacity 2 — a read after the 2nd send only.
func edgesBufCap2SecondSendNoEdge() int {
	x := 0
	ch := make(chan int, 2)
	done := make(chan int)
	go func() {
		x = 1
		<-ch
		<-ch
		<-ch
		done <- 0
	}()
	ch <- 0
	ch <- 0
	y := x
	ch <- 0
	<-done
	return y + x
}

// E9: close does not order a receive that returns a BUFFERED value: the
// closer writes x after its send and before the close; the receiver takes
// the value and reads x.
func edgesCloseThenBufferedValueRecvNoEdge() int {
	x := 0
	ch := make(chan int, 1)
	done := make(chan int)
	go func() {
		ch <- 5
		x = 1
		close(ch)
		done <- 0
	}()
	v := <-ch
	y := x
	<-done
	return v*10 + y
}

// E10: a select receiving the zero value from a closed channel acquires the
// close clock.
func edgesSelectRecvClosedAcquires() int {
	x := 0
	ch := make(chan int)
	done := make(chan int)
	go func() {
		x = 1
		close(ch)
		done <- 0
	}()
	select {
	case <-ch:
	}
	y := x
	<-done
	return y
}

// E11: `for range ch` ending on the close acquires.
func edgesRangeChanCloseAcquires() int {
	x := 0
	ch := make(chan int)
	done := make(chan int)
	go func() {
		x = 1
		close(ch)
		done <- 0
	}()
	n := 0
	for range ch {
		n++
	}
	y := x
	<-done
	return y*10 + n
}

// E12: the comma-ok receive of a closed channel acquires.
func edgesCommaOkClosedAcquires() int {
	x := 0
	ch := make(chan int)
	done := make(chan int)
	go func() {
		x = 1
		close(ch)
		done <- 0
	}()
	_, ok := <-ch
	y := x
	<-done
	if ok {
		return 9
	}
	return y
}

// E13: a write AFTER the close beside the zero-value receiver's read.
func edgesWriteAfterCloseRaces() int {
	x := 0
	ch := make(chan int)
	done := make(chan int)
	go func() {
		close(ch)
		x = 1
		done <- 0
	}()
	<-ch
	y := x
	<-done
	return y + x
}

// E14: two senders on one channel (the channel object read twice).
func edgesTwoSendersSameChan() int {
	a, b := 0, 0
	ch := make(chan int)
	go func() {
		a = 1
		ch <- 1
	}()
	go func() {
		b = 2
		ch <- 2
	}()
	s := <-ch + <-ch
	return s*100 + a*10 + b
}

// E16: a select's send clause with a default polls the channel object
// (selectgo pass 1's racereadpc, above the closed check) beside a close. On
// the schedules where the close lands first the polled send case panics
// (send on closed channel) — recovered in the child, as the BUG-046 row
// goroutines/select-closed-arrival/send-close-race does, so the oracle's run
// completes and its race report is the only crash evidence.
func edgesSelectDefaultSendPollVsClose() int {
	ch := make(chan int)
	done := make(chan int)
	go func() {
		defer func() {
			if recover() != nil {
				done <- 21
			} else {
				done <- 1
			}
		}()
		select {
		case ch <- 1:
		default:
		}
	}()
	close(ch)
	return <-done
}

// E17: a parked select receive beside the close (receive is acquire-only).
func edgesSelectRecvVsClose() int {
	ch := make(chan int)
	done := make(chan int)
	go func() {
		select {
		case <-ch:
		}
		done <- 0
	}()
	close(ch)
	<-done
	return 1
}

// E18: len(ch) beside a send.
func edgesLenChanVsSend() int {
	ch := make(chan int, 1)
	done := make(chan int)
	go func() {
		ch <- 1
		done <- 0
	}()
	n := len(ch)
	<-done
	return n*10 + len(ch)
}

// E18: cap(ch) beside a close.
func edgesCapChanVsClose() int {
	ch := make(chan int, 1)
	done := make(chan int)
	go func() {
		close(ch)
		done <- 0
	}()
	c := cap(ch)
	<-done
	return c
}

// E19: a goroutine's exit gives no edge: the child sends, then writes,
// then signals; main receives, reads, then waits.
func edgesExitNoEdge() int {
	x := 0
	done := make(chan int)
	done2 := make(chan int)
	go func() {
		done <- 0
		x = 1
		done2 <- 0
	}()
	<-done
	y := x
	<-done2
	return y + x
}

// E20: the go edge — a write before the go statement, read by the child.
func edgesSpawnEdgeWriteBefore() int {
	x := 0
	done := make(chan int)
	x = 1
	go func() {
		done <- x
	}()
	return <-done
}

// E21: a write after the go statement beside the child's read.
func edgesSpawnEdgeWriteAfter() int {
	x := 0
	done := make(chan int)
	go func() {
		done <- x
	}()
	x = 1
	y := <-done
	return y + x
}

// E22: a grandchild inherits the parent's clock.
func edgesGrandchildInheritsClock() int {
	x := 0
	done := make(chan int)
	x = 1
	go func() {
		go func() {
			done <- x
		}()
	}()
	return <-done
}

// E24: a transitive edge through two channels (A → B → main).
func edgesTransitiveTwoChans() int {
	x := 0
	c1 := make(chan int)
	c2 := make(chan int)
	go func() {
		x = 1
		c1 <- 0
	}()
	go func() {
		<-c1
		c2 <- 0
	}()
	<-c2
	return x
}

func main() {
	println(edgesGoValueRecvCopiedAtSpawn())
	println(edgesUnbufferedWrongDirection())
	println(edgesBufCap1SecondSendEdge())
	println(edgesBufCap1FirstSendNoEdge())
	println(edgesBufCap2ThirdSendEdge())
	println(edgesBufCap2SecondSendNoEdge())
	println(edgesCloseThenBufferedValueRecvNoEdge())
	println(edgesSelectRecvClosedAcquires())
	println(edgesRangeChanCloseAcquires())
	println(edgesCommaOkClosedAcquires())
	println(edgesWriteAfterCloseRaces())
	println(edgesTwoSendersSameChan())
	println(edgesSelectDefaultSendPollVsClose())
	println(edgesSelectRecvVsClose())
	println(edgesLenChanVsSend())
	println(edgesCapChanVsClose())
	println(edgesExitNoEdge())
	println(edgesSpawnEdgeWriteBefore())
	println(edgesSpawnEdgeWriteAfter())
	println(edgesGrandchildInheritsClock())
	println(edgesTransitiveTwoChans())
}
