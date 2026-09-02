package main

// Detector-soundness probes, SCHEDULE family: races that exist only on SOME
// schedules — the per-run nature of both oracles made visible. gc -race
// reports only on runs whose schedule co-executes the pair; the machine's
// enumerator refuses on exactly the paths that do (RACE-SOME), and a strict
// single default-stream run sees one path. Expected: machine RACE-SOME; gc
// RACE or DRF-in-N depending on the sampler's luck (recorded as counts).

// S-1: the child's DEFAULT path writes x; main writes x after filling the
// channel. Race iff the child polls before main's send lands.
func schedDefaultPathRace() int {
	x := 0
	ch := make(chan int, 1)
	done := make(chan int)
	go func() {
		select {
		case <-ch:
		default:
			x = 1
		}
		done <- 0
	}()
	ch <- 1
	x = 2
	<-done
	return x
}

// S-2: a race after a loop-carried handshake — three unbuffered exchanges,
// then unordered tail accesses on EVERY path (main's write follows its third
// send, the child's read follows its third receive; no edge between them).
// Expect agree-race with machine RACE-ALL (a schedule-INDEPENDENT race that
// needs the back-edge boundaries to be reached).
func schedTailRace() int {
	x := 0
	ch := make(chan int)
	done := make(chan int)
	go func() {
		for i := 0; i < 3; i++ {
			<-ch
		}
		r := x
		done <- r
	}()
	for i := 0; i < 3; i++ {
		ch <- i
	}
	x = 1
	return <-done
}

// S-3: the race needs the child to lose TWO polls in a row (a deeper path
// than S-1) — the sampler's odds shrink, the enumerator's coverage does not.
func schedDeepPathRace() int {
	x := 0
	ch := make(chan int, 1)
	done := make(chan int)
	go func() {
		n := 0
		for i := 0; i < 2; i++ {
			select {
			case <-ch:
				n++
			default:
			}
		}
		if n == 0 {
			x = 1
		}
		done <- 0
	}()
	ch <- 1
	x = 2
	<-done
	return x
}

func main() {
	println(schedDefaultPathRace(), schedTailRace(), schedDeepPathRace())
}
