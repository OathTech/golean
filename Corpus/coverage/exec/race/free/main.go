package main

// FALSE-POSITIVE guards for the race detector (channels arc slice 3):
// race-FREE programs whose accesses are ADJACENT to racy ones —
// distinct slice elements, distinct struct fields — at exactly the
// Loc-path granularity the detector records. `go run -race` is green
// on these; a raceDetected here is a detector granularity bug, never
// Go behavior. Strict-lane ok cases (deterministic observables).

// Disjoint slice elements: child writes s[0], main writes s[1] before
// the join — concurrent, but distinct memory locations.
func freeSliceDisjoint() int {
	s := make([]int, 2)
	done := make(chan int)
	go func() {
		s[0] = 3
		done <- 0
	}()
	s[1] = 4
	<-done
	return s[0]*10 + s[1]
}

type pair struct {
	a int
	b int
}

// Disjoint struct fields: distinct fields of one struct are distinct
// memory locations (spec §Type identity; TSan is byte-granular).
func freeFieldDisjoint() int {
	p := pair{}
	done := make(chan int)
	go func() {
		p.a = 5
		done <- 0
	}()
	p.b = 6
	<-done
	return p.a*10 + p.b
}

// READ/WRITE disjoint fields on a struct LOCAL: the direction that
// actually trips whole-cell footprints (S3 audit: the free lane's
// original guards were write/write only) — main reads p.a while the
// child writes p.b. Race-free; requires the fieldGet-chain narrowing.
func freeFieldReadWrite() int {
	p := pair{}
	p.a = 7
	done := make(chan int)
	go func() {
		p.b = 6
		done <- 0
	}()
	r := p.a
	<-done
	return r*10 + p.b
}

// READ/WRITE disjoint fields THROUGH A POINTER (*struct — the dominant
// raft-like idiom): the read is deref + fieldGet, narrowed to the
// field path.
func freePtrFieldReadWrite() int {
	p := &pair{}
	p.a = 3
	done := make(chan int)
	go func() {
		p.b = 4
		done <- 0
	}()
	r := p.a
	<-done
	return r*10 + p.b
}

// RED PIN (BUG-041): array-element READ via the value path (`a[1]` on
// an array local loads the whole cell before indexing) vs a concurrent
// DISJOINT-element write — race-free Go (-race green), refused by the
// recorded whole-cell over-approximation. Red until value-path element
// reads become path-precise; the over-refusal envelope is recorded in
// Race.lean and BUG-041.
func freeArrayReadWrite() int {
	var a [2]int
	a[1] = 9
	done := make(chan int)
	go func() {
		a[0] = 3
		done <- 0
	}()
	r := a[1]
	<-done
	return r*10 + a[0]
}

type fInner struct {
	x int
}

// VALUE receiver on the embedded type — promotion synthesizes a
// value-receiver wrapper on fOuter, so a *fOuter interface box
// dispatches with needsDeref.
func (i fInner) Get() int {
	return i.x
}

type fOuter struct {
	fInner
	z int
}

type fGetter interface {
	Get() int
}

// PROMOTED value-receiver method through a *T box vs a write to a
// NON-embedded field (S3 convergence, major): gc's synthesized
// (*fOuter).Get wrapper loads only the EMBEDDED field, so the
// concurrent o.z write is race-free — the dispatch footprint must
// narrow to the wrapper's hop path (the whole-pointee read would
// refuse this). The non-promoted control that must STAY racy is
// race/negative/iface-dispatch.
func freePromotedPtrBox() int {
	o := &fOuter{}
	o.x = 5
	var g fGetter = o
	done := make(chan int)
	go func() {
		o.z = 10
		done <- 0
	}()
	r := g.Get()
	<-done
	return r + o.z
}

// METHOD-VALUE creation concurrent with the pointee write, CALL after
// the join: gc defers the *T→T auto-deref to the call (probed), so
// this is race-free — pins that the model's callValCalleeK dispatch
// read fires at the call, not at creation.
func freeMethodValueOrder() int {
	p := &fInner{x: 1}
	var gv fGetter = p
	done := make(chan int)
	go func() {
		p.x = 2
		done <- 0
	}()
	f := gv.Get
	<-done
	return f()
}

// Write BEFORE the spawn, dispatch read in the child: ordered by the
// spawn edge — the free direction of the spawn-entry attribution pair
// (race/negative/spawn-dispatch is the racy direction).
func freeSpawnDispatch() int {
	p := &dispSBox{v: 5}
	var g dispSGetter = p
	ch := make(chan int)
	p.v = 6
	go g.Send(ch)
	return <-ch
}

type dispSBox struct {
	v int
}

func (b dispSBox) Send(ch chan int) {
	ch <- b.v
}

type dispSGetter interface {
	Send(ch chan int)
}

// BUG-056 acceptance (fix 2026-08-19): `&*p` is a nil-probe on the
// pointer VALUE, not a pointee access — gc compiles it to an
// uninstrumented TESTB (memo §2: TSan-green beside a concurrent
// pointee write, where a real `*p` read is TSan-red exit 66; both
// re-probed at the fix, artifacts/probe/addr056-accept, scratch).
// Main takes `&*p` and compares pointer identity while the child
// writes the POINTEE; the only pointee read is after the join. A fix
// that materialized a load (the rejected a1 desugar) turns this row
// red with a raceDetected refusal.
func freeAddrDerefNoRead() int {
	x := 0
	p := &x
	done := make(chan int)
	go func() {
		*p = 42
		done <- 1
	}()
	q := &*p
	same := 0
	if q == p {
		same = 1
	}
	<-done
	return same*100 + *q
}

// Q-RACEPATH (RULED [USER] 2026-08-31; implemented 2026-09-02): the
// CONSTANT-index narrowing's chain forms. index THEN field — `a[1].x`
// read beside an `a[0].x` write; gc reads one element field.
type freeArrElem struct {
	x int
}

func freeArrayConstIndexField() int {
	var a [2]freeArrElem
	a[1].x = 9
	done := make(chan int)
	go func() {
		a[0].x = 3
		done <- 0
	}()
	r := a[1].x
	<-done
	return r*10 + a[0].x
}

// field THEN constant index — `s.arr[1]` read beside an `s.arr[0]`
// write (fieldGet→indexGet chain).
type freeArrBox struct {
	arr [2]int
	n   int
}

func freeFieldArrayConstIndex() int {
	var s freeArrBox
	s.arr[1] = 9
	done := make(chan int)
	go func() {
		s.arr[0] = 3
		done <- 0
	}()
	r := s.arr[1]
	<-done
	return r*10 + s.arr[0]
}

// RED PIN (BUG-041 residual, O1): a DYNAMIC-index value-path array read
// `a[i]` (called with i = 1) beside a disjoint-element write — go/types
// cannot fold the index, so the base read stays whole-cell and the
// race-free program is refused. Over-refusal (fail-closed), recorded;
// the re-open trigger is in Race.lean's O1 entry.
func freeArrayDynIndexReadWrite(i int) int {
	var a [2]int
	a[1] = 9
	done := make(chan int)
	go func() {
		a[0] = 3
		done <- 0
	}()
	r := a[i]
	<-done
	return r*10 + a[0]
}

func main() {
	println(freeSliceDisjoint())
	println(freeFieldDisjoint())
	println(freeFieldReadWrite())
	println(freePtrFieldReadWrite())
	println(freeArrayReadWrite())
	println(freeArrayConstIndexField())
	println(freeFieldArrayConstIndex())
	println(freeArrayDynIndexReadWrite(1))
	println(freePromotedPtrBox())
	println(freeMethodValueOrder())
	println(freeSpawnDispatch())
	println(freeAddrDerefNoRead())
}
