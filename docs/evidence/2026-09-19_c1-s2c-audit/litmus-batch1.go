package main

import "sync"

// L01 — Once fast path: overwrite handed off via mutex; observer's Do after completion.
var muL01 sync.Mutex
var oL01 sync.Once
var xL01 int

func onceFastPathOverwrite() int {
	ch := make(chan int, 2)
	muL01.Lock()
	go func() {
		muL01.Lock()
		oL01.Do(func() { xL01 = 1 })
		muL01.Unlock()
		ch <- 0
	}()
	go func() {
		oL01.Do(func() { xL01 = 2 })
		ch <- 0
	}()
	oL01 = sync.Once{}
	muL01.Unlock()
	<-ch
	<-ch
	return xL01
}

// L02 — copy of the whole struct beside a Lock through a tag-compatible alias.
type sA struct {
	mu sync.Mutex
	f  int
}
type sB struct {
	mu sync.Mutex
	f  int
}

func aliasMutexCopyRoot() int {
	var s sA
	q := (*sB)(&s)
	done := make(chan int, 1)
	go func() {
		q.mu.Lock()
		q.f = 1
		q.mu.Unlock()
		done <- 0
	}()
	t := s
	<-done
	return t.f + s.f
}

// L03 — copy of a NESTED struct (field path) beside a Lock through the alias (BUG-080 x BUG-111).
type inA struct {
	mu sync.Mutex
	f  int
}
type outA struct {
	in inA
	g  int
}
type outB struct {
	in inA
	g  int
}

func aliasNestedMutexCopy() int {
	var o outA
	q := (*outB)(&o)
	done := make(chan int, 1)
	go func() {
		q.in.mu.Lock()
		q.in.f = 1
		q.in.mu.Unlock()
		done <- 0
	}()
	t := o.in
	<-done
	return t.f + o.in.f
}

// L03b — the same but the copy is sequenced AFTER the child's unlock via the join (must be clean).
func aliasNestedMutexCopyOrdered() int {
	var o outA
	q := (*outB)(&o)
	done := make(chan int, 1)
	go func() {
		q.in.mu.Lock()
		q.in.f = 1
		q.in.mu.Unlock()
		done <- 0
	}()
	<-done
	t := o.in
	return t.f + o.in.f
}

// L04 — HB edge through two spellings of ONE mutex; the data access through the original only.
type hA struct {
	mu sync.Mutex
	x  int
}
type hB struct {
	mu sync.Mutex
	x  int
}

func aliasMutexHandoff() int {
	var s hA
	q := (*hB)(&s)
	done := make(chan int, 1)
	go func() {
		q.mu.Lock()
		s.x = 2
		q.mu.Unlock()
		done <- 0
	}()
	s.mu.Lock()
	s.x = 1
	s.mu.Unlock()
	<-done
	return s.x
}

// L05 — embedded promotion: a.f vs a.inner.f name ONE word.
type inner struct{ f int }
type outer struct {
	inner
	g int
}

func promotedSameWord() int {
	var a outer
	done := make(chan int, 2)
	go func() {
		a.f = 1
		done <- 0
	}()
	go func() {
		_ = a.inner.f
		done <- 0
	}()
	<-done
	<-done
	return a.f
}

// L06 — shadowed field names at different depths: DIFFERENT words (must be clean).
type inner2 struct{ f int }
type outer2 struct {
	inner2
	f int
}

func shadowedDisjoint() int {
	var a outer2
	done := make(chan int, 1)
	go func() {
		a.inner2.f = 1
		done <- 0
	}()
	a.f = 2
	<-done
	return a.f*10 + a.inner2.f
}

// L07 — alias over a struct holding an array: same element vs disjoint elements.
type fA struct{ arr [2]int }
type fB struct{ arr [2]int }

func aliasArrayFieldSameElem() int {
	var s fA
	q := (*fB)(&s)
	done := make(chan int, 2)
	go func() {
		s.arr[1] = 1
		done <- 0
	}()
	go func() {
		_ = q.arr[1]
		done <- 0
	}()
	<-done
	<-done
	return s.arr[1]
}

func aliasArrayFieldDisjoint() int {
	var s fA
	q := (*fB)(&s)
	done := make(chan int, 1)
	go func() {
		q.arr[1] = 1
		done <- 0
	}()
	s.arr[0] = 2
	<-done
	return s.arr[0]*10 + s.arr[1]
}

// L08 — head-and-refill pairing: main's read after ONE receive is unordered with the child's write.
func headRefillUnordered() int {
	var x int
	ch := make(chan int, 1)
	ch <- 1
	go func() {
		x = 1
		ch <- 2
	}()
	v := <-ch
	_ = x
	<-ch
	return v
}

// L09 — the ordered twin: after BOTH receives the read is ordered (must be clean).
func headRefillOrdered() int {
	var x int
	ch := make(chan int, 1)
	ch <- 1
	go func() {
		x = 1
		ch <- 2
	}()
	v := <-ch
	<-ch
	_ = x
	return v
}

// L10 — close wakes MANY parked receivers; each acquires the closer's clock.
func closeWakesMany() int {
	var x int
	ch := make(chan int)
	done := make(chan int, 2)
	go func() {
		<-ch
		_ = x
		done <- 0
	}()
	go func() {
		<-ch
		_ = x
		done <- 0
	}()
	x = 1
	close(ch)
	<-done
	<-done
	return x
}

// L11 — WaitGroup.Wait wakes MANY waiters.
func wgWakesMany() int {
	var x int
	var wg sync.WaitGroup
	done := make(chan int, 2)
	wg.Add(1)
	go func() {
		wg.Wait()
		_ = x
		done <- 0
	}()
	go func() {
		wg.Wait()
		_ = x
		done <- 0
	}()
	x = 1
	wg.Done()
	<-done
	<-done
	return x
}

// L12 — a spawn whose child's first step spawns; the grandchild's write is joined by a channel.
func nestedSpawnClean() int {
	var x int
	done := make(chan int, 1)
	go func() {
		go func() {
			x = 1
			done <- 0
		}()
	}()
	<-done
	return x
}

func nestedSpawnRacy() int {
	var x int
	done := make(chan int, 1)
	go func() {
		go func() {
			x = 1
			done <- 0
		}()
	}()
	x = 2
	<-done
	return x
}

// L13 — select-to-select rendezvous (the machine refuses upstream; what does it say?).
func selectSelectRendezvous() int {
	var x int
	ch := make(chan int)
	done := make(chan int, 1)
	go func() {
		x = 7
		select {
		case ch <- 1:
		}
		done <- 0
	}()
	var v int
	select {
	case v = <-ch:
	}
	<-done
	return v + x
}

// L14 — recv wakes a blocked sender (unbuffered): both directions ordered.
func recvWakesSenderClean() int {
	var x, y int
	ch := make(chan int)
	done := make(chan int, 1)
	go func() {
		x = 1
		ch <- 1
		_ = y
		done <- 0
	}()
	<-ch
	_ = x
	y = 1
	<-done
	return x
}

// L14b — buffered: the child's write AFTER its committed send is unordered with main's read.
func bufferedSendThenWriteRacy() int {
	var x int
	ch := make(chan int, 1)
	done := make(chan int, 1)
	go func() {
		ch <- 1
		x = 1
		done <- 0
	}()
	<-ch
	_ = x
	<-done
	return x
}

// L15 — select receive target written by the select (pre-existing question: gc's raceWriteObjectPC before racenotify).
func selectRecvTargetOrder() int {
	var x int
	ch := make(chan int, 1)
	go func() {
		x = 1
		ch <- 5
	}()
	select {
	case x = <-ch:
	}
	return x
}

// L16 — plain receive target written by the receive.
func recvTargetOrder() int {
	var x int
	ch := make(chan int, 1)
	go func() {
		x = 1
		ch <- 5
	}()
	x = <-ch
	return x
}

// L17 — Unlock's tail through the alias vs a copy under the lock (BUG-080 pin class; control).
func aliasUnlockTailCopy() int {
	var s sA
	q := (*sB)(&s)
	done := make(chan int, 1)
	go func() {
		q.mu.Lock()
		q.mu.Unlock()
		done <- 0
	}()
	s.mu.Lock()
	t := s
	s.mu.Unlock()
	<-done
	return t.f
}

// L18 — channel object through an alias: parked send via q.ch vs close via c.ch (control: both refuse).
type cA struct{ ch chan int }
type cB struct{ ch chan int }

func aliasChanObjClose() int {
	var c cA
	c.ch = make(chan int)
	q := (*cB)(&c)
	done := make(chan int, 1)
	go func() {
		defer func() { recover(); done <- 0 }()
		q.ch <- 1
	}()
	close(c.ch)
	<-done
	return 1
}
