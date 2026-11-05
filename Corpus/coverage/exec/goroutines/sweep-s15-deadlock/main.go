package main

import "sync"

// Sweep S15 (scheduling boundaries and the menu), group F: the deadlock
// terminal when nobody is runnable (latitude inventory C9: gc's
// detector counts every goroutine parked on a Go-visible primitive —
// channels, select, the sync primitives — and the machine's
// `deadlockOrRefusal` classifies the empty menu the same way). The
// existing rows park everybody on one kind; these mix the kinds: a
// WaitGroup wait beside a mutex, a receive beside a nested Once, a
// select beside an RLock under a held writer, a wait beside a nil
// channel, a receive beside a send to a full buffer, and `select {}`
// beside a parked child. The matrix is in docs/defect-shapes.md (S15).

// F3: main waits on the group; the child waits on the mutex main holds.
func mixedWgMutex() int {
	var mu sync.Mutex
	var wg sync.WaitGroup
	mu.Lock()
	wg.Add(1)
	go func() {
		mu.Lock()
		wg.Done()
	}()
	wg.Wait()
	return 0
}

// F4: main waits on an unbuffered receive; the child is parked in a
// nested `once.Do`.
func mixedRecvOnce() int {
	var once sync.Once
	ch := make(chan int)
	go func() {
		once.Do(func() {
			once.Do(func() {})
		})
		ch <- 1
	}()
	return <-ch
}

// F5: main selects over two channels nobody sends on; the child waits
// for a read lock under main's held write lock.
func mixedSelectRlock() int {
	var rw sync.RWMutex
	a := make(chan int)
	b := make(chan int)
	rw.Lock()
	go func() {
		rw.RLock()
		a <- 1
	}()
	select {
	case v := <-a:
		return v
	case v := <-b:
		return v
	}
}

// F6: main waits on the group; the child is parked on a nil channel.
func mixedWgNilChan() int {
	var wg sync.WaitGroup
	var nilch chan int
	wg.Add(1)
	go func() {
		<-nilch
		wg.Done()
	}()
	wg.Wait()
	return 0
}

// F7: main waits on a receive; the child is parked on a send to a FULL
// buffered channel.
func fullBufferSend() int {
	ch := make(chan int, 1)
	res := make(chan int)
	ch <- 1
	go func() {
		ch <- 2
		res <- 1
	}()
	return <-res
}

// F9: main blocks on `select {}` while the child is parked on a
// channel.
func selectEmptyWithParkedChild() int {
	ch := make(chan int)
	go func() {
		<-ch
	}()
	select {}
}

func main() {
	mixedWgMutex()
	mixedRecvOnce()
	mixedSelectRlock()
	mixedWgNilChan()
	fullBufferSend()
	selectEmptyWithParkedChild()
}
