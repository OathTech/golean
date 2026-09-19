package main

import (
	"sync"
	"sync/atomic"
)

// B2-01 — WaitGroup word through a NESTED alias: the first waiter's sema WRITE vs a copy of the inner struct.
type wgIn struct {
	wg sync.WaitGroup
	f  int
}
type wgOutA struct {
	in wgIn
	g  int
}
type wgOutB struct {
	in wgIn
	g  int
}

func wgAliasNestedCopyBesideWait() int {
	var o wgOutA
	q := (*wgOutB)(&o)
	done := make(chan int, 1)
	o.in.wg.Add(1)
	go func() {
		q.in.wg.Wait()
		done <- 0
	}()
	t := o.in
	o.in.wg.Done()
	<-done
	return t.f
}

// B2-02 — Once through two spellings: the observer's acquire must see the completer's release.
type oA struct {
	o sync.Once
	x int
}
type oB struct {
	o sync.Once
	x int
}

func onceAliasObserve() int {
	var s oA
	q := (*oB)(&s)
	done := make(chan int, 1)
	go func() {
		q.o.Do(func() { s.x = 1 })
		done <- 0
	}()
	s.o.Do(func() { s.x = 1 })
	_ = s.x
	<-done
	return s.x
}

// B2-03 — sync/atomic clock table through two spellings of ONE address.
type atA struct {
	flag int32
	x    int
}
type atB struct {
	flag int32
	x    int
}

func atomicAliasHandoff() int {
	var s atA
	q := (*atB)(&s)
	done := make(chan int, 1)
	go func() {
		s.x = 1
		atomic.StoreInt32(&s.flag, 1)
		done <- 0
	}()
	r := 0
	if atomic.LoadInt32(&q.flag) == 1 {
		r = s.x
	}
	<-done
	return r
}

// B2-04 — RWMutex through two spellings: writer under q.mu, reader under s.mu.
type rwA struct {
	mu sync.RWMutex
	x  int
}
type rwB struct {
	mu sync.RWMutex
	x  int
}

func rwAliasHandoff() int {
	var s rwA
	q := (*rwB)(&s)
	done := make(chan int, 1)
	go func() {
		q.mu.Lock()
		s.x = 2
		q.mu.Unlock()
		done <- 0
	}()
	s.mu.RLock()
	_ = s.x
	s.mu.RUnlock()
	<-done
	return s.x
}

// B2-05 — cap-2 chan struct{}: gc realizes ONE sync object (acquire+release per op); the machine two slots.
func chanStructAccum() int {
	var x int
	ch := make(chan struct{}, 2)
	done := make(chan int, 1)
	go func() {
		ch <- struct{}{}
		x = 1
		ch <- struct{}{}
		done <- 0
	}()
	<-ch
	_ = x
	<-ch
	<-done
	return x
}

// B2-06 — the int twin of B2-05: two real slots in gc as well (race in every schedule).
func chanIntTwoSlots() int {
	var x int
	ch := make(chan int, 2)
	done := make(chan int, 1)
	go func() {
		ch <- 1
		x = 1
		ch <- 2
		done <- 0
	}()
	<-ch
	_ = x
	<-ch
	<-done
	return x
}

// B2-07 — Mutex TryLock through an alias: success acquires the (one) clock.
type tlA struct {
	mu sync.Mutex
	x  int
}
type tlB struct {
	mu sync.Mutex
	x  int
}

func tryLockAliasHandoff() int {
	var s tlA
	q := (*tlB)(&s)
	done := make(chan int, 1)
	s.mu.Lock()
	s.x = 1
	s.mu.Unlock()
	go func() {
		if q.mu.TryLock() {
			_ = s.x
			q.mu.Unlock()
		}
		done <- 0
	}()
	<-done
	return s.x
}

// B2-08 — a close-woken sender beside a receiver: the closer's write vs the parked sender's entry read (control: refuses).
func closeWakesSender() int {
	ch := make(chan int)
	done := make(chan int, 1)
	go func() {
		defer func() { recover(); done <- 0 }()
		ch <- 1
	}()
	close(ch)
	<-done
	return 1
}

// B2-09 — select commit's poll: a send clause on channel A polled while another goroutine closes A (BUG-046 class control).
func selectPollVsClose() int {
	a := make(chan int, 1)
	b := make(chan int, 1)
	done := make(chan int, 1)
	b <- 1
	go func() {
		close(a)
		done <- 0
	}()
	select {
	case a <- 1:
	case <-b:
	}
	<-done
	return 1
}
