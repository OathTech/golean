package main

// A child goroutine's print AFTER main's, joined through a channel: the
// only observable order is main first, child second (strict lane).
func goroutineOrdered() int {
	println("first (main)")
	done := make(chan int)
	go func() {
		println("second (child)")
		done <- 1
	}()
	<-done
	println("third (main)")
	return 0
}
