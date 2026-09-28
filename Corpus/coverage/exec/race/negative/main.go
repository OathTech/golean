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
// arm; no other shape exercises it). Also the NON-promoted control
// for race/free/promoted-ptr-box: a direct value-receiver method
// really does copy the whole pointee, so this must STAY racy.
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

// Send signals completion through a channel — the spawn-entry
// dispatch shape (`go g.Send(ch)`).
func (b dispBox) Send(ch chan int) {
	ch <- b.v
}

type dispSender interface {
	Send(ch chan int)
}

// METHOD VALUE dispatch (callValCalleeK arm): the *T→T auto-deref
// happens at the CALL, not at `f := g.Get` creation (gc-probed), so a
// call concurrent with the pointee write races.
func raceMethodValue() int {
	p := &dispBox{v: 1}
	var g dispGetter = p
	f := g.Get
	done := make(chan int)
	go func() {
		p.v = 2
		done <- 0
	}()
	r := f()
	<-done
	return r
}

// DEFERRED interface-method call (the frame-drain dispatch arms): the
// deref read happens at the drain, concurrent with the child's write.
func raceDeferDispatch() int {
	p := &dispBox{v: 3}
	var g dispGetter = p
	done := make(chan int)
	go func() {
		p.v = 4
		done <- 0
	}()
	func() {
		defer g.Get()
	}()
	<-done
	return p.v
}

// SPAWN-entry dispatch (`go g.Send(ch)`): the auto-deref read is
// attributed to the CHILD (after the spawn edge), so the parent's
// post-spawn write races it — pins the child-id attribution direction
// (a parent-attributed read would be sequenced with the write and
// silently green).
func raceSpawnDispatch() int {
	p := &dispBox{v: 5}
	var g dispSender = p
	ch := make(chan int)
	go g.Send(ch)
	p.v = 6
	return <-ch
}

type promInner struct {
	x int
}

// VALUE receiver on the embedded type: promotion through outer gives
// a synthesized VALUE-receiver wrapper on promOuter.
func (i promInner) Get() int {
	return i.x
}

type promOuter struct {
	promInner
	z int
}

// PROMOTED dispatch with a REAL race on the embedded field: the
// narrowed wrapper read (.promInner) must still overlap the child's
// write INSIDE the embedded field — the red direction of the
// promotion narrowing (its green direction is
// race/free/promoted-ptr-box).
func racePromotedDispatch() int {
	o := &promOuter{}
	var g dispGetter = o
	done := make(chan int)
	go func() {
		o.x = 7
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

// Q-RACEPATH's must-stay-racy direction (implemented 2026-09-02): the
// constant-index narrowing records `a[1]` at its ELEMENT path, so a
// concurrent write to the SAME element still conflicts (equal paths) …
func raceArrayConstIndexSameElem() int {
	var a [2]int
	done := make(chan int)
	go func() {
		a[1] = 4
		done <- 0
	}()
	r := a[1]
	<-done
	return r
}

// … and a concurrent WHOLE-array write still conflicts (the array's
// path is a prefix of the element's).
func raceArrayConstIndexWholeWrite() int {
	var a [2]int
	done := make(chan int)
	go func() {
		a = [2]int{7, 8}
		done <- 0
	}()
	r := a[1]
	<-done
	return r
}

// G-P S0 must-stay-racy guards for race/free/promoted-ptr-hop: through
// the embedded-POINTER hop the promoted value-receiver dispatch loads
// the embedded pointer field and then the pointee, so a concurrent
// write to the hop's TARGET field (o.promHopInner.x) or to the embedded
// POINTER field itself (o.promHopInner) races (gc -race reports both).
// The narrowing G-P S2 introduces must keep refusing both.
type promHopInner struct {
	x int
}

func (i promHopInner) Get() int {
	return i.x
}

type promHopOuter struct {
	*promHopInner
	z int
}

func racePromotedPtrHopTarget() int {
	o := &promHopOuter{promHopInner: &promHopInner{x: 1}}
	var g dispGetter = o
	done := make(chan int)
	go func() {
		o.promHopInner.x = 7
		done <- 0
	}()
	r := g.Get()
	<-done
	return r
}

func racePromotedPtrHopField() int {
	o := &promHopOuter{promHopInner: &promHopInner{x: 1}}
	var g dispGetter = o
	done := make(chan int)
	go func() {
		o.promHopInner = &promHopInner{x: 7}
		done <- 0
	}()
	r := g.Get()
	<-done
	return r
}

func main() {
	println(racePromotedPtrHopTarget())
	println(racePromotedPtrHopField())
	println(raceWriteWrite())
	println(raceReadWrite())
	println(raceIncrement())
	println(raceMapRW())
	println(raceSliceElem())
	println(raceIfaceDispatch())
	println(raceLenMap())
	println(raceMapRangeIter())
	println(raceMethodValue())
	println(raceDeferDispatch())
	println(raceSpawnDispatch())
	println(racePromotedDispatch())
	println(raceArrayConstIndexSameElem())
	println(raceArrayConstIndexWholeWrite())
	println(raceStructTagAliasField())
	println(raceStructTagAliasArrayField())
}

// BUG-111 (found by the C1 S0 frame-law spike, 2026-09-18; fix (i) RULED
// [USER] 2026-09-18): ONE memory word, two SPELLINGS. `aliasA` and `aliasB`
// are struct-tag-compatible (identical field lists), so `(*aliasB)(&a)` is a
// legal pointer conversion and `q.f` names the very word `a.f` names. The
// child's write and the other child's read are HB-unordered on every
// schedule; `go run -race` keys by ADDRESS and reports. A detector keyed by
// the structural path with its static typeId (`.field a aliasA "f"` vs
// `.field a aliasB "f"`) sees two disjoint keys and MISSES the race — so
// this row is BORN on the wrong side (the machine accepts a racy program:
// baseline FAIL, on BUG-111's Cases: line) and flips to PASS with the
// canonical-path keys. Main's readout is ordered after both children by
// the two receives.
type aliasA struct{ f int }
type aliasB struct{ f int }

func raceStructTagAliasField() int {
	var a aliasA
	q := (*aliasB)(&a)
	done := make(chan int, 2)
	go func() {
		a.f = 1
		done <- 0
	}()
	go func() {
		_ = q.f
		done <- 0
	}()
	<-done
	<-done
	return a.f
}

// BUG-111 audit F1 (C1 S2c fix round, 2026-09-19): the alias race on an
// ARRAY-ELEMENT field — the `.data` key with an `.index` step under a
// struct-tag-compatible alias. One child writes `s.arr[1]`, the other reads
// `q.arr[1]` — the same word by ADDRESS, HB-unordered on every schedule;
// `go run -race` reports it (RACE 5/5 at GOMAXPROCS 1 and 8). Structural
// keys (`.index (.field s aliasArrA "arr") 1` vs `.index (.field s aliasArrB
// "arr") 1`) miss it: main's binary at the fix round ACCEPTED the program
// on every enumerated path (a HOLE); the canonical keys refuse on every
// path. Born PASS under the fix; pins that `Loc.canon` keeps the `.index`
// step while erasing the field step's typeId. Main's readout is ordered
// after both children by the two receives.
type aliasArrA struct{ arr [2]int }
type aliasArrB struct{ arr [2]int }

func raceStructTagAliasArrayField() int {
	var s aliasArrA
	q := (*aliasArrB)(&s)
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
