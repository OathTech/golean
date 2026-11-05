package main

// Sweep S15 (scheduling boundaries and the menu), group A: the operations
// outside the registry that read or write shared or observable state —
// BUG-123's class (`len(ch)` and `print` opened no scheduling boundary).
// Each subject is a neighbour of the fixed instances: the channel-length
// read beside a peer's RECEIVE and beside a CLOSE, `cap(ch)`, the length
// of an unbuffered channel beside a parked sender, a multi-operand
// `println`, a print in a deferred call (normal drain and panic
// unwinding) and a print inside a called function. The matrix is in
// docs/defect-shapes.md (S15) and BUG-123's Neighbourhood line.

// A pure, registry-free delay (a finite recursion: no loop back-edge, no
// registry op), as in goroutines/sched-dependent and builtins/print/
// goroutine-gap: it makes gc exhibit the peer's action between two reads
// at a useful rate; the machine's set does not depend on it.
//
//go:noinline
func s15Delay(n int) int {
	if n == 0 {
		return 0
	}
	return n + s15Delay(n-1)
}

// A2: two `len(ch)` reads around a pure delay while a child DRAINS one
// element of a pre-filled cap-2 buffer. The receive may land before the
// first read (11), between the two (21) or after both (22).
func lenPeerRecv() int {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	done := make(chan int)
	go func() {
		<-ch
		done <- 1
	}()
	a := len(ch)
	_ = s15Delay(100)
	b := len(ch)
	<-done
	return 10*a + b
}

// A3: `len(ch)` beside a peer's `close`: closing never changes the
// buffer count (spec#Close: buffered values are still delivered), so the
// two reads agree on every schedule and the closed channel still hands
// out its one element, then the zero value with ok=false.
func lenBesideClose() int {
	ch := make(chan int, 2)
	ch <- 1
	done := make(chan int)
	go func() {
		close(ch)
		done <- 1
	}()
	a := len(ch)
	_ = s15Delay(100)
	b := len(ch)
	<-done
	v, ok := <-ch
	_, ok2 := <-ch
	r := 10*a + b + v*10000
	if ok {
		r += 100
	}
	if !ok2 {
		r += 1000
	}
	return r
}

// A4: `cap(ch)` twice around a pure delay beside a peer's send — a
// channel's capacity never changes, so the read observes no peer
// (the sched-boundary design argued `cap` is not a boundary).
func capBesideSend() int {
	ch := make(chan int, 3)
	done := make(chan int)
	go func() {
		ch <- 1
		done <- 1
	}()
	a := cap(ch)
	_ = s15Delay(100)
	b := cap(ch)
	<-done
	<-ch
	return 10*a + b
}

// A5: `len` of an UNBUFFERED channel beside a sender that may be parked
// on it: gc's chanlen reads the buffer count, which an unbuffered channel
// never has — 0 on every schedule, and the value arrives by pairing.
func lenUnbufferedParkedSender() int {
	ch := make(chan int)
	ready := make(chan int, 1)
	go func() {
		ready <- 1
		ch <- 7
	}()
	<-ready
	a := len(ch)
	_ = s15Delay(100)
	b := len(ch)
	v := <-ch
	return 100*v + 10*a + b
}

// A8: ONE `println` with several operands is ONE statement under gc's
// printlock, so a peer's `println` lands before or after the whole line,
// never between its operands.
func printlnMultiOperandAtomic() int {
	done := make(chan int, 1)
	go func() {
		println("x", "y", "z")
		done <- 1
	}()
	println("a", "b", "c")
	<-done
	return 0
}

// A9: a print in a DEFERRED call at the child's normal drain, beside
// main's print: A lands before B, between B and D, or after D.
func deferredPrintDrain() int {
	done := make(chan int, 1)
	go func() {
		defer func() {
			print("D")
			done <- 1
		}()
		print("B")
	}()
	print("A")
	<-done
	return 0
}

// A10: a print in a deferred call DURING PANIC UNWINDING (post-raise,
// recovered), beside main's print: the unwinding goroutine's deferred
// print is a scheduling point like any print, so A may land between
// B and R.
func deferredPrintUnwinding() int {
	done := make(chan int, 1)
	go func() {
		defer func() {
			_ = recover()
			print("R")
			done <- 1
		}()
		print("B")
		panic("x")
	}()
	print("A")
	<-done
	return 0
}

//go:noinline
func s15SayB() {
	print("B")
}

// A11: a print inside a CALLED function — a call is no scheduling point,
// the print inside it is.
func printInsideCallee() int {
	done := make(chan int, 1)
	go func() {
		s15SayB()
		done <- 1
	}()
	print("A")
	<-done
	return 0
}

func main() {
	lenPeerRecv()
	lenBesideClose()
	capBesideSend()
	lenUnbufferedParkedSender()
	printlnMultiOperandAtomic()
	deferredPrintDrain()
	deferredPrintUnwinding()
	printInsideCallee()
}
