package main

import "sync"

// Sweep S15 (scheduling boundaries and the menu), group D: spawn and
// goroutine exit — BUG-040's class (the post-spawn reschedule point) and
// the deferred-call drain at a goroutine's exit. The argument receive of
// a `go` statement in the spawner; the four deferred drains a waiting
// peer observes (`println`, `wg.Done`, `close`, `mu.Unlock`); three
// printing children (a menu of width 4); and a child spawning a
// grandchild. The matrix is in docs/defect-shapes.md (S15).

// D2: the `go` statement's argument is received in the SPAWNER before
// the child exists (spec#Go_statements), so the child always sees 5.
func goArgRecv() int {
	ch := make(chan int, 1)
	res := make(chan int, 1)
	ch <- 5
	go func(v int) {
		res <- v * 2
	}(<-ch)
	return <-res
}

// D6: a deferred print at the child's normal drain (the deferred-literal
// spelling: `defer println("d")` of the builtin is frontend-quarantined
// by name, a coverage gap recorded in the sweep); main's `a` lands
// before `b`, between `b` and `d`, or after `d`.
func deferPrintlnDrain() int {
	done := make(chan int, 1)
	go func() {
		defer func() {
			done <- 1
		}()
		defer func() {
			println("d")
		}()
		println("b")
	}()
	println("a")
	<-done
	return 0
}

// D6: a deferred `wg.Done()` at the drain orders the child's `B` before
// main's `A` on every schedule.
func deferDoneDrain() int {
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		print("B")
	}()
	wg.Wait()
	print("A")
	return 0
}

// D6: a deferred `close(ch)` at the drain wakes main's receive after
// the child's `B`.
func deferCloseDrain() int {
	ch := make(chan int)
	go func() {
		defer close(ch)
		print("B")
	}()
	<-ch
	print("A")
	return 0
}

// D6: a deferred `mu.Unlock()` at the drain releases main's `Lock`
// after the child's `B`.
func deferUnlockDrain() int {
	var mu sync.Mutex
	started := make(chan int)
	go func() {
		mu.Lock()
		defer mu.Unlock()
		started <- 1
		print("B")
	}()
	<-started
	mu.Lock()
	print("A")
	mu.Unlock()
	return 0
}

// D9: three children each print one byte — a menu of width 4 and six
// orders.
func threePrinters() int {
	done := make(chan int, 3)
	go func() {
		print("a")
		done <- 1
	}()
	go func() {
		print("b")
		done <- 1
	}()
	go func() {
		print("c")
		done <- 1
	}()
	<-done
	<-done
	<-done
	return 0
}

// D10: a child spawns a grandchild; `m`, `c` and `g` are concurrent
// (the grandchild exists only after the child's spawn, which has no
// print before it).
func grandchildPrints() int {
	done := make(chan int, 2)
	go func() {
		go func() {
			print("g")
			done <- 1
		}()
		print("c")
		done <- 1
	}()
	print("m")
	<-done
	<-done
	return 0
}

func main() {
	goArgRecv()
	deferPrintlnDrain()
	deferDoneDrain()
	deferCloseDrain()
	deferUnlockDrain()
	threePrinters()
	grandchildPrints()
}
