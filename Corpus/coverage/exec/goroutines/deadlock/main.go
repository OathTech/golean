package main

// MULTI-goroutine deadlock (slice 2's generalization of the slice-1
// immediate terminal): the detector state is ALL goroutines asleep —
// runnable-until-blocked histories included. Go oracle: exit status 2,
// "fatal error: all goroutines are asleep - deadlock!". NEVER run
// under -race (the detector is suppressed there — ground-truth §5).

func deadlockMutual() int {
	a := make(chan int)
	b := make(chan int)
	go func() {
		<-a // parks forever
	}()
	return <-b // parks; now ALL goroutines are asleep
}

func deadlockChain() int {
	a := make(chan int)
	b := make(chan int)
	c := make(chan int)
	go func() {
		b <- <-a // parks receiving a
	}()
	go func() {
		c <- <-b // parks receiving b
	}()
	return <-c // parks; nobody ever sends a
}

// The workers RUN (a real rendezvous completes) before the wedge: the
// deadlock terminal must classify histories, not just first steps.
func deadlockAfterProgress() int {
	work := make(chan int)
	stuck := make(chan int)
	go func() {
		v := <-work // completes: main sends 4
		<-stuck     // parks forever
		_ = v
	}()
	work <- 4
	return <-stuck // parks; all asleep
}

// A parked SELECT participates in the all-asleep state.
func deadlockWithSelect() int {
	a := make(chan int)
	b := make(chan int)
	go func() {
		select {
		case <-a:
		case b <- 1:
		}
	}()
	// Main parks on a FRESH channel, so neither of the select's clauses
	// ever has a partner: all goroutines are asleep.
	<-make(chan int)
	return 0
}

func main() {
	deadlockMutual()
}
