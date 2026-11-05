package main

// S16 sweep, matrix E26 (the defect-neighbourhood campaign, lane sweep/s16-race,
// 2026-10-27): the completion of init is synchronized before main, and the go
// statement before the child — so an init-time write is ordered before a
// main-spawned goroutine's read.

var initX int

func init() {
	initX = 1
}

func initEdgeWriteMainGoroutineRead() int {
	done := make(chan int)
	go func() {
		done <- initX
	}()
	return <-done
}

func main() {
	println(initEdgeWriteMainGoroutineRead())
}
