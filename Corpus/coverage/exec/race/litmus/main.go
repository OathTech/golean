package main

// LITMUS PAIRS (channels arc slice 3; validation note lane e): the
// weak-memory litmus shapes in channel-SYNCHRONIZED form (race-free —
// must admit exactly the SC outcomes; the confluent ones are strict
// go-run equality at full strength) and in racy shared-variable form
// (must refuse: raceDetected on every tested stream, `go run -race`
// red as the justifying oracle). Together they pin the DRF-SC boundary
// executably: SC inside DRF, refusal outside.
//
// Each green case here doubles as a HAPPENS-BEDGE-EDGE discriminator
// for the detector — it exercises exactly one go_mem channel rule, and
// a missing edge would surface as a false raceDetected on a race-free
// program.

// Message passing, channel-synchronized (go_mem: "A send on a channel
// is synchronized before the completion of the corresponding receive").
// Confluent: the stale read (0) must be UNREACHABLE — every schedule
// returns 42.
func litmusMPSync() int {
	data := 0
	flag := make(chan int, 1)
	go func() {
		data = 42
		flag <- 1
	}()
	<-flag
	return data
}

// Message passing, racy shared-variable form: flag and data are plain
// variables — main's reads race the child's writes on every schedule.
func litmusMPRacy() int {
	data := 0
	flag := 0
	done := make(chan int)
	go func() {
		data = 42
		flag = 1
		done <- 0
	}()
	f := flag
	d := data
	<-done
	return f*100 + d
}

// Load-buffering shape, racy form: each side reads the other's
// variable and writes its own — every access pair is HB-unordered.
func litmusLBRacy() int {
	x := 0
	y := 0
	done := make(chan int)
	go func() {
		a := x
		y = a + 1
		done <- 0
	}()
	b := y
	x = b + 1
	<-done
	return b
}

// Close edge (go_mem: "The closing of a channel is synchronized before
// a receive that returns a zero value because the channel is closed").
// Deterministic: main parks, wakes on the close, reads 9.
func litmusCloseHB() int {
	data := 0
	ch := make(chan int)
	go func() {
		data = 9
		close(ch)
	}()
	<-ch
	return data
}

// The buffered k/k+C edge (go_mem: "The kth receive on a channel with
// capacity C is synchronized before the k+Cth send from that channel
// completes") — the counting-semaphore/mutex idiom on a cap-1 channel:
// main's x access is sequenced before its release (<-mu, receive 1),
// which synchronizes before the child's acquire (mu <- 1, send 2)
// completes. Race-free, deterministic result 2.
func litmusChanMutex() int {
	x := 0
	mu := make(chan int, 1)
	done := make(chan int)
	mu <- 1
	go func() {
		mu <- 1
		x = x + 1
		<-mu
		done <- 0
	}()
	x = x + 1
	<-mu
	<-done
	return x
}

// Store-buffering shape in channel form: each side "publishes" on its
// own cap-1 channel, then polls the other with select/default. The
// receives are destructive, but the SC-forbidden corner is the same:
// r1 = 0 requires T1's poll to precede T2's publish, which places T1's
// publish before T2's poll, forcing r2 = 1 — so {01, 10, 11} is the
// admitted set and 00 is SC-FORBIDDEN. Schedule-dependent observable:
// declared membership; the slice-4 enumerator-over-schedules owns
// certifying the set (red until then, like sched-dependent/*).
func litmusSBChan() int {
	x := make(chan int, 1)
	y := make(chan int, 1)
	r1ch := make(chan int)
	r2ch := make(chan int)
	go func() {
		x <- 1
		select {
		case <-y:
			r1ch <- 1
		default:
			r1ch <- 0
		}
	}()
	go func() {
		y <- 1
		select {
		case <-x:
			r2ch <- 1
		default:
			r2ch <- 0
		}
	}()
	r1 := <-r1ch
	r2 := <-r2ch
	return r1*10 + r2
}

func main() {
	println(litmusMPSync())
	println(litmusMPRacy())
	println(litmusLBRacy())
	println(litmusCloseHB())
	println(litmusChanMutex())
	println(litmusSBChan())
}
