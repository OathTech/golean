package main

// Audit pins (channels-arc-s1 audit S1/S7): a receive STATEMENT with a
// failing target follows spec §Assignments' two phases — the RECEIVE is
// phase 1, the store (and its nil-deref / out-of-range panic) is phase
// 2. So Go performs the communication first: the channel is DRAINED
// even when the store then panics, and a bad target never turns a
// blocking receive into a panic (an empty channel deadlocks the
// single-goroutine program before any store panic can fire).

func recvIntoPtr(p *int, ch chan int) (hit int) {
	defer func() {
		if recover() != nil {
			hit = 1
		}
	}()
	*p = <-ch
	return 0
}

func recvIntoIdx(xs []int, i int, ch chan int) (hit int) {
	defer func() {
		if recover() != nil {
			hit = 1
		}
	}()
	xs[i] = <-ch
	return 0
}

func recvNilDerefTargetRecovered() int {
	ch := make(chan int, 1)
	ch <- 7
	var p *int
	return recvIntoPtr(p, ch) * 100
}

// THE drain discriminator: the recovered store panic must leave the
// channel EMPTY (the receive happened), len(ch) == 0.
func recvNilDerefTargetDrains() int {
	ch := make(chan int, 1)
	ch <- 7
	var p *int
	return recvIntoPtr(p, ch)*100 + len(ch)
}

func recvOobTargetDrains() int {
	ch := make(chan int, 1)
	ch <- 9
	xs := []int{1}
	return recvIntoIdx(xs, 7, ch)*100 + len(ch)
}

// Phase order decides the CLASSIFICATION too: with an empty channel the
// receive blocks (deadlock), and the nil-deref store panic never fires.
func recvBadTargetBlocks() int {
	ch := make(chan int)
	var p *int
	*p = <-ch
	return 0
}

func main() {
	recvNilDerefTargetRecovered()
}
