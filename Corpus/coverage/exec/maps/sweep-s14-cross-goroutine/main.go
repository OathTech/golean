package main

// S14 sweep (lane sweep/s14-map-iter, 2026-10-27; members BUG-005, BUG-088):
// mutation from ANOTHER goroutine, DRF by a req/ack handshake over
// unbuffered channels (every map access HB-ordered; `go run -race` green),
// at the mutation kinds the existing cross-goroutine rows do not hold
// (delete of a produced key, delete + re-add, clear: maps/cross-goroutine-*):
// a delete of an UNREACHED key, an insert, an update of the unreached
// entries; the range itself running on a spawned goroutine; and foreign
// READS during a range with no synchronisation at all — reads against the
// pick's reads are not a race (the racy delete/insert twins are
// maps/cross-goroutine-delete-readd/racy and race/negative/map-range-iter).

// foreign-delete-unreached: the helper deletes the next key in cyclic order
// after the first production — unreached, never produced: {112, 1012, 1102}.
func s14ForeignDeleteUnreached() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	req := make(chan int)
	ack := make(chan int)
	go func() {
		k := <-req
		delete(m, k%3+1)
		ack <- 0
	}()
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		if n == 1 {
			req <- k
			<-ack
		}
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + len(m)
}

// foreign-insert: the helper inserts key 4 after the first production — a
// created entry, produced or skipped: {1110, 1111}.
func s14ForeignInsert() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	req := make(chan int)
	ack := make(chan int)
	go func() {
		<-req
		m[4] = 4
		ack <- 0
	}()
	c := map[int]int{}
	n := 0
	for k := range m {
		n++
		if n > 8 {
			return -1
		}
		c[k]++
		if n == 1 {
			req <- k
			<-ack
		}
	}
	return c[1]*1000 + c[2]*100 + c[3]*10 + c[4]
}

// foreign-update-unreached: the helper sets the unreached entries to 100
// after the first production; their productions read the live values:
// {2013, 2023, 2033} as sum*10 + len.
func s14ForeignUpdateUnreached() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	req := make(chan int)
	ack := make(chan int)
	go func() {
		k := <-req
		for i := 1; i <= 3; i++ {
			if i != k {
				m[i] = 100
			}
		}
		ack <- 0
	}()
	n, sum := 0, 0
	for k, v := range m {
		n++
		if n > 8 {
			return -1
		}
		sum += v
		if n == 1 {
			req <- k
			<-ack
		}
	}
	return sum*10 + len(m)
}

// range-on-goroutine: the range runs on a spawned goroutine, deleting the
// current key and creating k+10 for the start keys: {33, 42, 51, 60}.
func s14RangeOnGoroutine() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	done := make(chan int)
	go func() {
		n := 0
		for k := range m {
			n++
			if n > 8 {
				break
			}
			delete(m, k)
			if k < 10 {
				m[k+10] = k
			}
		}
		done <- n
	}()
	n := <-done
	return n*10 + len(m)
}

// foreign-reads: an index read and len by another goroutine during the
// range with no synchronisation — reads only, so no race on any schedule.
func s14ForeignReads() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	done := make(chan int)
	go func() {
		s := m[1] + len(m)
		done <- s
	}()
	sum := 0
	for k := range m {
		sum += k
	}
	return sum*10 + <-done
}

func main() {
	println(s14ForeignDeleteUnreached())
	println(s14ForeignInsert())
	println(s14ForeignUpdateUnreached())
	println(s14RangeOnGoroutine())
	println(s14ForeignReads())
}
