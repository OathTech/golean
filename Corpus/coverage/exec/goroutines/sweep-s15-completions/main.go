package main

import (
	"sync"
	"sync/atomic"
)

// Sweep S15 (scheduling boundaries and the menu), group C: the
// registry-op COMPLETIONS — BUG-152's post-op class (`ChoiceSite.postOp`,
// `Config.completedFlag`). Every registry op that wakes or releases a
// partner, followed by the issuer's private print beside the partner's
// print: the pairing of an unbuffered send, a receive, a close, a select
// commit on each clause kind, a select default-take (NOT a completion:
// no flag — the print itself is the boundary), a woken select, Unlock,
// Done, Once, RUnlock, an atomic, and a registry op that panics and is
// recovered. The matrix is in docs/defect-shapes.md (S15).

// C2: an UNBUFFERED send pairs with the receiver; afterwards the sender's
// `S` and the receiver's `R` are concurrent.
func unbufferedPairPrints() int {
	ch := make(chan int)
	done := make(chan int, 1)
	go func() {
		<-ch
		print("R")
		done <- 1
	}()
	ch <- 1
	print("S")
	<-done
	return 0
}

// C3: a receive completes; the receiver's `R` and the sender's later
// `S` are concurrent.
func recvThenPrint() int {
	ch := make(chan int, 1)
	done := make(chan int, 1)
	go func() {
		ch <- 1
		print("S")
		done <- 1
	}()
	<-ch
	print("R")
	<-done
	return 0
}

// C4: `close` wakes a parked receiver; the closer's `C` and the woken
// receiver's `R` are concurrent.
func closeWakePrints() int {
	ch := make(chan int)
	ready := make(chan int, 1)
	done := make(chan int, 1)
	go func() {
		ready <- 1
		<-ch
		print("R")
		done <- 1
	}()
	<-ready
	close(ch)
	print("C")
	<-done
	return 0
}

// C5: a `select` whose SEND clause commits.
func selectCommitSendPrints() int {
	ch := make(chan int, 1)
	done := make(chan int, 1)
	go func() {
		<-ch
		print("R")
		done <- 1
	}()
	select {
	case ch <- 1:
		print("S")
	}
	<-done
	return 0
}

// C5: a `select` whose RECEIVE clause commits.
func selectCommitRecvPrints() int {
	ch := make(chan int, 1)
	done := make(chan int, 1)
	go func() {
		ch <- 1
		print("S")
		done <- 1
	}()
	select {
	case <-ch:
		print("R")
	}
	<-done
	return 0
}

// C6: a `select` takes its `default` (no registry op completes, so no
// post-op flag); the print after it is the next scheduling point.
func selectDefaultPrints() int {
	ch := make(chan int)
	done := make(chan int, 1)
	go func() {
		print("B")
		done <- 1
	}()
	select {
	case <-ch:
		print("X")
	default:
		print("D")
	}
	<-done
	return 0
}

// C7: a `select` that may PARK and be woken by the child's send.
func selectWakePrints() int {
	ch := make(chan int)
	done := make(chan int, 1)
	go func() {
		ch <- 1
		print("S")
		done <- 1
	}()
	select {
	case <-ch:
		print("R")
	}
	<-done
	return 0
}

// C8: `Unlock` releases a parked locker; `U` and `L` are concurrent.
func unlockWakePrints() int {
	var mu sync.Mutex
	done := make(chan int, 1)
	mu.Lock()
	go func() {
		mu.Lock()
		print("L")
		mu.Unlock()
		done <- 1
	}()
	mu.Unlock()
	print("U")
	<-done
	return 0
}

// C9: `Done` wakes `Wait`; `D` and `W` are concurrent.
func doneWakePrints() int {
	var wg sync.WaitGroup
	done := make(chan int, 1)
	wg.Add(1)
	go func() {
		wg.Done()
		print("D")
		done <- 1
	}()
	wg.Wait()
	print("W")
	<-done
	return 0
}

// C10: two callers of one `Once`: `F` runs exactly once, before either
// caller's own print; `A` and `B` are concurrent.
func onceWakePrints() int {
	var once sync.Once
	done := make(chan int, 1)
	f := func() {
		print("F")
	}
	go func() {
		once.Do(f)
		print("B")
		done <- 1
	}()
	once.Do(f)
	print("A")
	<-done
	return 0
}

// C11: `RUnlock` releases a pending writer; `R` and `W` are concurrent.
func runlockWakeWriterPrints() int {
	var rw sync.RWMutex
	done := make(chan int, 1)
	rw.RLock()
	go func() {
		rw.Lock()
		print("W")
		rw.Unlock()
		done <- 1
	}()
	rw.RUnlock()
	print("R")
	<-done
	return 0
}

// C12: an atomic op (the typed wrapper's Add) completes on each side;
// the prints after them are concurrent; the sum after the join is 11.
func atomicThenPrint() int {
	var f atomic.Int32
	done := make(chan int, 1)
	go func() {
		f.Add(1)
		print("S")
		done <- 1
	}()
	f.Add(10)
	print("M")
	<-done
	return int(f.Load())
}

// C14: a registry op that PANICS (a send on a closed channel) and is
// recovered opens no post-op flag; the print after the recovery is the
// next scheduling point, so `A` and the child's `B` are concurrent.
func recoveredSendClosedPrints() int {
	ch := make(chan int, 1)
	done := make(chan int, 1)
	close(ch)
	go func() {
		print("B")
		done <- 1
	}()
	func() {
		defer func() {
			_ = recover()
		}()
		ch <- 1
	}()
	print("A")
	<-done
	return 0
}

func main() {
	unbufferedPairPrints()
	recvThenPrint()
	closeWakePrints()
	selectCommitSendPrints()
	selectCommitRecvPrints()
	selectDefaultPrints()
	selectWakePrints()
	unlockWakePrints()
	doneWakePrints()
	onceWakePrints()
	runlockWakeWriterPrints()
	atomicThenPrint()
	recoveredSendClosedPrints()
}
