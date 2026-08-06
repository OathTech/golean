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

// Delta-review pin (D3): spec §Assignments phase 2 carries the stores
// out LEFT-TO-RIGHT — the first target's store is observable even when
// the second target's store panics (the spec's own x[1], x[3] = 4, 5
// example shape, with the receive drained first).
func recvIntoTwo(vp *int, okp *bool, ch chan int) (hit int) {
	defer func() {
		if recover() != nil {
			hit = 1
		}
	}()
	*vp, *okp = <-ch
	return 0
}

func recvSecondTargetPanicStoresFirst() int {
	ch := make(chan int, 1)
	ch <- 5
	v := 0
	var okp *bool
	hit := recvIntoTwo(&v, okp, ch)
	return hit*1000 + v*10 + len(ch)
}

// Convergence-round pins (BUG-029): spec §Assignments' two phases must
// stay SPLIT in the delivery path. Phase 1 evaluates the target
// address OPERANDS (left-to-right, after the communication — the
// drain pins above); phase 2 carries the stores out left-to-right,
// with the outer address operation's nil/bounds check a STORE-TIME
// event. Collapsing them either direction diverges:
//   - store-then-evaluate-next interleaves phase 1 with stores
//     (dep-index-target reads the FIRST target's post-store value;
//     nil-index-base-second stores before a phase-1 operand panic);
//   - evaluate-addresses-eagerly fires phase-2 checks early
//     (field-second-target / oob-second-target lose the first store).

// Phase-1 operand capture: bs[i]'s index operand i reads the
// PRE-STORE value 0 even though i itself is assigned first in phase 2.
func recvDepIndexTarget() int {
	ch := make(chan int, 1)
	ch <- 3
	i := 0
	bs := []bool{false, false, false, false}
	i, bs[i] = <-ch
	n := i * 100
	for j := range bs {
		if bs[j] {
			n += j + 1
		}
	}
	return n
}

// Phase-1 operand panic: the second target's index BASE (*bp) is an
// operand of the index expression — its nil deref fires in phase 1,
// BEFORE any store (xs[0] must remain 0).
func recvNilIndexBaseSecond() int {
	ch := make(chan int, 1)
	ch <- 3
	xs := []int{0}
	var bp *[]bool
	hit := 0
	func() {
		defer func() {
			if recover() != nil {
				hit = 1
			}
		}()
		xs[0], (*bp)[0] = <-ch
	}()
	return hit*1000 + xs[0]*50
}

// Phase-2 store-time panic: a nil FIELD target (p.b with nil p) is the
// assignment's own implicit indirection — it fires at the STORE, after
// the first target's store landed (xs[0] == 3).
type recvT struct{ b bool }

func recvFieldSecondTarget() int {
	ch := make(chan int, 1)
	ch <- 3
	xs := []int{0}
	var p *recvT
	hit := 0
	func() {
		defer func() {
			if recover() != nil {
				hit = 1
			}
		}()
		xs[0], p.b = <-ch
	}()
	return hit*1000 + xs[0]*50
}

// Phase-2 store-time panic, bounds flavor: bs[9]'s bounds check is a
// store-time event — the first store lands before it fires.
func recvOobSecondTarget() int {
	ch := make(chan int, 1)
	ch <- 3
	xs := []int{0}
	bs := []bool{false}
	hit := 0
	func() {
		defer func() {
			if recover() != nil {
				hit = 1
			}
		}()
		xs[0], bs[9] = <-ch
	}()
	return hit*1000 + xs[0]*50
}
