package main

import "sync"

// Train-19 shake probes for DC11: a genuine Go deadlock in every parked shape
// must still be the `deadlock` terminal, never a refusal.

func nilRecv() int {
	var c chan int
	return <-c
}

func nilSend() int {
	var c chan int
	c <- 1
	return 1
}

func unbufferedSend() int {
	c := make(chan int)
	c <- 1
	return 1
}

func bufferedFullSend() int {
	c := make(chan int, 1)
	c <- 1
	c <- 2
	return 1
}

func selectNoDefault() int {
	a := make(chan int)
	var b chan int
	select {
	case v := <-a:
		return v
	case b <- 1:
		return 2
	}
}

func selectEmpty() int {
	select {}
}

func mutexTwice() int {
	var m sync.Mutex
	m.Lock()
	m.Lock()
	return 1
}

func rwWriterThenReader() int {
	var m sync.RWMutex
	m.Lock()
	m.RLock()
	return 1
}

func rwReaderThenWriter() int {
	var m sync.RWMutex
	m.RLock()
	m.Lock()
	return 1
}

func wgWait() int {
	var wg sync.WaitGroup
	wg.Add(1)
	wg.Wait()
	return 1
}

func onceRecursive() int {
	var o sync.Once
	o.Do(func() { o.Do(func() {}) })
	return 1
}

// mixed: two goroutines parked on each other's channels, main on a third
func mixed() int {
	a, b, c := make(chan int), make(chan int), make(chan int)
	go func() { a <- <-b }()
	go func() { b <- <-a }()
	return <-c
}

// goroutine parked on a mutex, main on a channel it will never get
func mixedSync() int {
	var m sync.Mutex
	c := make(chan int)
	m.Lock()
	go func() { m.Lock(); c <- 1 }()
	return <-c
}

// main exits while another goroutine is parked: ok, not deadlock
func mainExitsParked() int {
	c := make(chan int)
	go func() { <-c }()
	return 7
}

func main() {
	println(mainExitsParked())
}
