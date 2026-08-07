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

func main() {
	println(freeSliceDisjoint())
	println(freeFieldDisjoint())
	println(freeFieldReadWrite())
	println(freePtrFieldReadWrite())
	println(freeArrayReadWrite())
}
