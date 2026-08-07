package main

// A parked select woken by a PARTNER's arrival (slice-1's
// .blockedSelect resumed by the slice-2 pool): the wake path with
// exactly one candidate is deterministic — the L2 multi-ready envelope
// stays slice 4.

func selectWakeRecv() int {
	ch := make(chan int)
	go func() {
		ch <- 5 // pairs with the parked select's receive clause
	}()
	select {
	case v := <-ch:
		return v * 11
	}
}

func selectWakeSend() int {
	ch := make(chan int)
	done := make(chan int)
	go func() {
		done <- <-ch // pairs with the parked select's send clause
	}()
	select {
	case ch <- 6:
	}
	return <-done
}

func selectWakeClosed() int {
	ch := make(chan int)
	done := make(chan int)
	go func() {
		select {
		case v, ok := <-ch:
			if ok {
				done <- v
			} else {
				done <- 44 // woken by close: drained zero, ok=false
			}
		}
	}()
	close(ch)
	return <-done
}

func selectWakeBufferedData() int {
	ch := make(chan int, 1)
	done := make(chan int)
	go func() {
		select {
		case v := <-ch:
			done <- v * 2 // woken when the buffer gains data
		}
	}()
	ch <- 9
	return <-done
}

func main() {
	selectWakeRecv()
	selectWakeSend()
	selectWakeClosed()
	selectWakeBufferedData()
}
