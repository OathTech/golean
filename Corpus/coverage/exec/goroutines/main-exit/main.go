package main

// Main-exit semantics (D6, spec §Program execution: "It does not wait
// for other (non-main) goroutines to complete"; probe p17): the
// subject's return terminates the program; leaked goroutines — and
// their defers — are observably nothing (exit 0).

func mainExitLeavesBlockedGoroutine() int {
	ch := make(chan int)
	go func() {
		<-ch // parks forever; killed at main exit
	}()
	return 7
}

func mainExitLeavesTwo() int {
	a := make(chan int)
	go func() { a <- 1 }() // parks forever (nobody receives)
	go func() { <-a }()    // may pair with the sender, or not — either way unobserved
	return 13
}

func main() {
	mainExitLeavesBlockedGoroutine()
	mainExitLeavesTwo()
}
