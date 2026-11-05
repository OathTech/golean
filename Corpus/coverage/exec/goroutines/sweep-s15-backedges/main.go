package main

import "sync"

// Sweep S15 (scheduling boundaries and the menu), group B: the loop
// re-entry shapes — BUG-152's back-edge class (`ChoiceSite.backEdge`:
// `.next (.loop …)`, `.signal .cont (.loop …)`, `.next (.mapIterK …)`).
// Every loop form a goroutine can spin in, printing one `s` per
// iteration after a wake-producing send, beside main's print `m` after
// the wake; and three pollers that spin until a peer's action becomes
// visible through a registry op, a channel-length read or a mutex. The
// labelled-continue and goto forms travel the `contTo` path, which has
// no back-edge arm (docs/2026-10-06_spin-bounds.md §2.1) — their
// bounded, printing shapes are pinned here; their unbounded pure
// spinners are hand probes recorded in BUG-152's Neighbourhood line.
// The matrix is in docs/defect-shapes.md (S15).

// B2: a three-clause `for` printing twice.
func forClauseInterleave() int {
	ch := make(chan int, 1)
	done := make(chan int, 1)
	go func() {
		ch <- 1
		for i := 0; i < 2; i++ {
			print("s")
		}
		done <- 1
	}()
	<-ch
	print("m")
	<-done
	return 0
}

// B3: range over an integer.
func rangeIntInterleave() int {
	ch := make(chan int, 1)
	done := make(chan int, 1)
	go func() {
		ch <- 1
		for range 2 {
			print("s")
		}
		done <- 1
	}()
	<-ch
	print("m")
	<-done
	return 0
}

// B4: range over a slice.
func rangeSliceInterleave() int {
	ch := make(chan int, 1)
	done := make(chan int, 1)
	go func() {
		ch <- 1
		for range []int{1, 2} {
			print("s")
		}
		done <- 1
	}()
	<-ch
	print("m")
	<-done
	return 0
}

// B5: range over a channel — the producer prints `p` after its
// unbuffered send pairs, the consumer prints `c` after the receive, and
// the close ends the range (one element keeps the tree small: the
// two-element shape closes only at 7.7 M work units, past the row budget).
func rangeChanInterleave() int {
	ch := make(chan int)
	done := make(chan int, 1)
	go func() {
		for range ch {
			print("c")
		}
		done <- 1
	}()
	ch <- 1
	print("p")
	close(ch)
	<-done
	return 0
}

// B6: range over a map (the `mapIterK` re-entry; the iteration order
// pick is consumed but unobserved).
func rangeMapInterleave() int {
	ch := make(chan int, 1)
	done := make(chan int, 1)
	m := map[int]int{1: 1, 2: 2}
	go func() {
		ch <- 1
		for range m {
			print("s")
		}
		done <- 1
	}()
	<-ch
	print("m")
	<-done
	return 0
}

// B7: the body ends in a bare `continue` (`.signal .cont (.loop …)`).
func continueInterleave() int {
	ch := make(chan int, 1)
	done := make(chan int, 1)
	go func() {
		ch <- 1
		for i := 0; i < 2; i++ {
			print("s")
			continue
		}
		done <- 1
	}()
	<-ch
	print("m")
	<-done
	return 0
}

// B8: `continue` from inside a `switch` inside the loop.
func continueInSwitchInterleave() int {
	ch := make(chan int, 1)
	done := make(chan int, 1)
	go func() {
		ch <- 1
		for i := 0; i < 2; i++ {
			print("s")
			switch {
			default:
				continue
			}
		}
		done <- 1
	}()
	<-ch
	print("m")
	<-done
	return 0
}

// B9: `continue` from inside a `select` with a `default` clause.
func continueInSelectInterleave() int {
	ch := make(chan int, 1)
	done := make(chan int, 1)
	go func() {
		ch <- 1
		for i := 0; i < 2; i++ {
			print("s")
			select {
			default:
				continue
			}
		}
		done <- 1
	}()
	<-ch
	print("m")
	<-done
	return 0
}

// B10: a labelled `continue L` to the enclosing loop (the `contTo`
// signal re-enters the loop head without the back-edge arm).
func continueLabelInterleave() int {
	ch := make(chan int, 1)
	done := make(chan int, 1)
	go func() {
		ch <- 1
		i := 0
	L:
		for {
			if i >= 2 {
				break L
			}
			i++
			print("s")
			continue L
		}
		done <- 1
	}()
	<-ch
	print("m")
	<-done
	return 0
}

// B11: a labelled `continue outer` from an inner loop.
func continueOuterLabelInterleave() int {
	ch := make(chan int, 1)
	done := make(chan int, 1)
	go func() {
		ch <- 1
	outer:
		for i := 0; i < 2; i++ {
			for j := 0; j < 5; j++ {
				print("s")
				continue outer
			}
		}
		done <- 1
	}()
	<-ch
	print("m")
	<-done
	return 0
}

// B12: a `goto` loop (the frontend's dispatch-loop restructuring emits
// a labelled `continue-to`), in a named function so the label sits at
// the function body's top level.
//
//go:noinline
func s15GotoTwice() {
	i := 0
top:
	if i < 2 {
		i++
		print("s")
		goto top
	}
}

func gotoInterleave() int {
	ch := make(chan int, 1)
	done := make(chan int, 1)
	go func() {
		ch <- 1
		s15GotoTwice()
		done <- 1
	}()
	<-ch
	print("m")
	<-done
	return 0
}

// B14: a goroutine polls `select` with `default` in a loop until main
// sends; the polling branches that never see the send are counted as
// non-terminating by the `iters=` budget, never as members.
func selectDefaultPoll() int {
	done := make(chan int, 1)
	res := make(chan int, 1)
	go func() {
		for {
			select {
			case v := <-done:
				res <- v
				return
			default:
			}
		}
	}()
	done <- 42
	return <-res
}

// B15: a goroutine polls `len(ch)` until main's buffered send lands.
func lenPoll() int {
	ch := make(chan int, 1)
	res := make(chan int, 1)
	go func() {
		for len(ch) == 0 {
		}
		res <- <-ch
	}()
	ch <- 7
	return <-res
}

// B16: a goroutine polls a mutex-protected flag until main sets it.
func mutexPoll() int {
	var mu sync.Mutex
	flag := 0
	res := make(chan int, 1)
	go func() {
		for {
			mu.Lock()
			v := flag
			mu.Unlock()
			if v != 0 {
				res <- v
				return
			}
		}
	}()
	mu.Lock()
	flag = 5
	mu.Unlock()
	return <-res
}

func main() {
	forClauseInterleave()
	rangeIntInterleave()
	rangeSliceInterleave()
	rangeChanInterleave()
	rangeMapInterleave()
	continueInterleave()
	continueInSwitchInterleave()
	continueInSelectInterleave()
	continueLabelInterleave()
	continueOuterLabelInterleave()
	gotoInterleave()
	selectDefaultPoll()
	lenPoll()
	mutexPoll()
}
