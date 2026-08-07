package main

// RACY-NEGATIVE lane (channels arc slice 3, D2+D3(b); validation note
// lane d): every subject has a DATA RACE on every interleaving — the
// conflicting accesses are unordered by happens-before no matter how
// the scheduler picks — so the machine must refuse (raceDetected) on
// every tested stream, and `go run -race` is the justifying second
// oracle (TSan: no false positives; a red report is a real race).
// These cases are NEVER combined with deadlock expectations (the -race
// runtime suppresses the deadlock detector — ground-truth note §5).

// Write/write: main's x = 2 is sequenced before its receive, the
// child's x = 1 before its send — the two writes are HB-unordered on
// every schedule.
func raceWriteWrite() int {
	x := 0
	done := make(chan int)
	go func() {
		x = 1
		done <- 0
	}()
	x = 2
	<-done
	return x
}

// Read/write: main reads x concurrently with the child's write.
func raceReadWrite() int {
	x := 5
	done := make(chan int)
	go func() {
		x = 7
		done <- 0
	}()
	y := x
	<-done
	return y + x
}

// The classic unsynchronized counter: both sides read-modify-write.
func raceIncrement() int {
	x := 0
	done := make(chan int)
	go func() {
		x = x + 1
		done <- 0
	}()
	x = x + 1
	<-done
	return x
}

// Concurrent map read and map write: the map object is one location
// for race purposes (matches gc/TSan's classification).
func raceMapRW() int {
	m := map[int]int{1: 10}
	done := make(chan int)
	go func() {
		m[2] = 20
		done <- 0
	}()
	v := m[1]
	<-done
	return v
}

// Same slice ELEMENT written by both goroutines (the disjoint-element
// contrast case is race/free/slice-disjoint).
func raceSliceElem() int {
	s := make([]int, 2)
	done := make(chan int)
	go func() {
		s[0] = 1
		done <- 0
	}()
	s[0] = 2
	<-done
	return s[0] + s[1]
}

type dispBox struct {
	v int
}

type dispGetter interface {
	Get() int
}

// VALUE receiver: a *dispBox in the interface auto-dereferences the
// pointee at dispatch (the receiver is copied out of *p) — a genuine
// read of shared memory.
func (b dispBox) Get() int {
	return b.v
}

// Interface pointer-box dispatch read vs a concurrent write to the
// pointee (S3 audit, major: the auto-deref read happens at FRAME
// ENTRY — dynamicDispatch's needsDeref — and needs its own footprint
// arm; no other shape exercises it).
func raceIfaceDispatch() int {
	p := &dispBox{v: 1}
	var g dispGetter = p
	done := make(chan int)
	go func() {
		p.v = 2
		done <- 0
	}()
	r := g.Get()
	<-done
	return r
}

// len(m) beside a concurrent map write: gc's maps.Map length read IS
// instrumented on go1.26.5 (S3 audit refuted the earlier
// "len is invisible to -race" claim for maps) — the map object is one
// location, and len reads it.
func raceLenMap() int {
	m := map[int]int{}
	done := make(chan int)
	go func() {
		m[1] = 1
		done <- 0
	}()
	n := len(m)
	<-done
	return n + len(m)
}

// Map WRITE landing while another goroutine's range is ACTIVE (between
// handoffs): gc's mapIterNext reads the map on every iteration, so
// -race flags the write against iteration 2. Our machine snapshots the
// entries at range entry (BUG-005), performs no per-iteration read,
// and returns a value — a PERMANENT red pin carried by BUG-005 until
// the live-iteration surgery lands (the fix's footprint arm falls out
// of that surgery).
func raceMapRangeIter() int {
	m := map[int]int{1: 1, 2: 2}
	ch := make(chan int)
	go func() {
		for range m {
			ch <- 1
		}
		close(ch)
	}()
	s := <-ch // iteration 1 handed off; the range is ACTIVE
	m[3] = 3
	// Drain to the close: gc's LIVE iteration may or may not visit the
	// new key (spec latitude), so the count varies — irrelevant here,
	// the race lane compares only the refusal, never values.
	for v := range ch {
		s += v
	}
	return s + len(m)
}

func main() {
	println(raceWriteWrite())
	println(raceReadWrite())
	println(raceIncrement())
	println(raceMapRW())
	println(raceSliceElem())
	println(raceIfaceDispatch())
	println(raceLenMap())
	println(raceMapRangeIter())
}
