package main

import "sync"

var flag int

// Acquisition ORDER between two contenders is the L1 scheduling
// latitude (design note §6: no spec/package text on acquisition order
// — gc realizes semaphore FIFO with barging, one legal point of the
// schedule envelope). Whether main's critical section runs before or
// after the worker's is schedule-dependent: members {10, 20}. All flag
// accesses are under the mutex (race-free); the channel join only
// closes the run.
func acquisitionOrder() int {
	flag = 0
	var m sync.Mutex
	done := make(chan int)
	go func() {
		m.Lock()
		flag = 1
		m.Unlock()
		done <- 1
	}()
	m.Lock()
	r := 0
	if flag == 0 {
		r = 10
	} else {
		r = 20
	}
	m.Unlock()
	<-done
	return r
}

func main() {
	acquisitionOrder()
}
