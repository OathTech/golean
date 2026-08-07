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

func main() {
	println(freeSliceDisjoint())
	println(freeFieldDisjoint())
}
