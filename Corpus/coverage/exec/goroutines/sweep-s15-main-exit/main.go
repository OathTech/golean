package main

import (
	"sync"
	"sync/atomic"
)

// Sweep S15 (scheduling boundaries and the menu), group E: main's exit
// — BUG-044's class (the L5 main-exit window: spec#Program_execution
// gives no ordering between main's return and the others' progress) —
// and the abort beside a peer. The leaked parks of every kind (`select
// {}`, a mutex main holds, `wg.Wait`, a nested `once.Do`); a child woken
// by main's last op whose continuation prints; a spinning child; a
// child's pending deferred print; main's panic beside a parked child;
// main's LAST observable a registry op (send, atomic, unlock) then a
// panic — the post-op flag opens the window the abort itself never
// does (BUG-159, the ruled limit, is hand-probed, not rowed); and a
// printer beside a panicker. The matrix is in docs/defect-shapes.md
// (S15).

// E2: main exits while a child is parked on `select {}` forever.
func leakedSelectEmpty() int {
	go func() {
		select {}
	}()
	return 1
}

// E3: main exits holding a mutex the child waits for.
func leakedMutex() int {
	var mu sync.Mutex
	mu.Lock()
	go func() {
		mu.Lock()
	}()
	return 1
}

// E3: main exits while a child waits on a WaitGroup nobody completes.
func leakedWgWait() int {
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		wg.Wait()
	}()
	return 1
}

// E3: main exits while a child is parked in a nested `once.Do`.
func leakedOnceNested() int {
	var once sync.Once
	go func() {
		once.Do(func() {
			once.Do(func() {})
		})
	}()
	return 1
}

// E4: main's last op wakes the child, whose continuation prints `B`;
// the window lets the print land or not.
func wokenChildPrints() int {
	ch := make(chan int)
	go func() {
		<-ch
		print("B")
	}()
	ch <- 1
	return 1
}

// E5: main exits while a child spins in a registry-free loop (the
// spinning branches are non-terminating, never members).
func spinningChild() int {
	go func() {
		for {
		}
	}()
	return 1
}

// E6: main's last op wakes a child whose exit has a deferred print (the
// deferred-literal spelling; `defer print("D")` of the builtin is
// frontend-quarantined by name).
func childDeferredPrint() int {
	ch := make(chan int)
	go func() {
		defer func() {
			print("D")
		}()
		<-ch
	}()
	ch <- 1
	return 1
}

// E9: main panics while the child is parked forever — the child never
// runs on any schedule.
func panicChildParked() int {
	ch := make(chan int)
	go func() {
		<-ch
		print("never")
	}()
	panic("boom")
}

// E15: main's last observable is a SEND that wakes the child, then a
// panic: the post-op flag after the send is the window in which `B`
// may land before the abort.
func opThenPanicSend() int {
	ch := make(chan int, 1)
	go func() {
		<-ch
		print("B")
	}()
	ch <- 1
	panic("x")
}

// E15: the same with an atomic store the child spins on.
func opThenPanicAtomic() int {
	var f int32
	go func() {
		for atomic.LoadInt32(&f) == 0 {
		}
		print("B")
	}()
	atomic.StoreInt32(&f, 1)
	panic("x")
}

// E15: the same with an Unlock the child waits for.
func opThenPanicUnlock() int {
	var mu sync.Mutex
	mu.Lock()
	go func() {
		mu.Lock()
		print("B")
	}()
	mu.Unlock()
	panic("x")
}

// E16: one child prints, another panics; main waits for the printer.
// Main's return may win against the runnable panicker (ok with `B`), or
// the abort lands with or without `B`.
func printerBesidePanicker() int {
	done := make(chan int, 1)
	go func() {
		print("B")
		done <- 1
	}()
	go func() {
		panic("x")
	}()
	<-done
	return 1
}

func main() {
	leakedSelectEmpty()
	leakedMutex()
	leakedWgWait()
	leakedOnceNested()
	wokenChildPrints()
	spinningChild()
	childDeferredPrint()
	printerBesidePanicker()
	opThenPanicSend()
	opThenPanicAtomic()
	opThenPanicUnlock()
	panicChildParked()
}
