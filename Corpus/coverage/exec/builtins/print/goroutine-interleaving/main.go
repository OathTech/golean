package main

// Two children print concurrently: the two lines interleave by the
// SCHEDULE (latitude inventory R18: the L1 envelope — gc's `printlock`
// makes each statement atomic, so the members are the two line orders,
// never a byte interleaving). Membership lane: observed ∈ {ab, ba}.
func goroutineInterleaving() int {
	done := make(chan int, 2)
	go func() {
		println("a")
		done <- 1
	}()
	go func() {
		println("b")
		done <- 1
	}()
	<-done
	<-done
	return 0
}
