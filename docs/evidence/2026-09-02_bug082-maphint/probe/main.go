// BUG-082 side-effect probe family — make(map[K]V, hint) with an effectful
// hint, gc vs the machine (docs/evidence/2026-09-02_bug082-maphint/README.md).
// One function per probe; `go run .` prints every gc value; the machine
// runs each function from the frontend's wire via
// `golean native-json-run --function <name>`.
package main

import "fmt"

func bump(p *int) int {
	*p = *p + 2
	return *p
}

// The maxAlloc auditor's shape: the hint's call bumps n (gc: 3).
func probeBump() int {
	n := 1
	m := make(map[int]int, bump(&n))
	m[1] = 2
	return n*10 + len(m)
}

// Two calls in one hint expression, both evaluated (gc: n = 5).
func probeBumpTwice() int {
	n := 1
	m := make(map[int]int, bump(&n)+bump(&n))
	return n*10 + len(m)
}

// The hint's call returns a NEGATIVE: evaluated, clamped, the map works.
func probeNegBump() int {
	n := -9
	m := make(map[int]int, bump(&n))
	m[1] = 2
	m[2] = 3
	return n*100 + len(m)*10 + m[2]
}

// A panicking hint: the panic happens; `created` never flips.
func probeHintPanic() (result int) {
	created := 0
	defer func() {
		if recover() != nil {
			result = created*10 + 1
		}
	}()
	m := make(map[int]int, panicHint())
	created = 1
	m[1] = 2
	return created*10 + len(m)
}

func panicHint() int {
	panic("hint")
}

// Order relative to neighbouring calls (digits: before, hint, key, value).
func probeOrder() int {
	log := 0
	logd(&log, 1)
	m := make(map[int]int, logd(&log, 2))
	m[logd(&log, 3)] = logd(&log, 4)
	return log*10 + len(m)
}

func logd(p *int, d int) int {
	*p = *p*10 + d
	return d
}

func main() {
	fmt.Println("probeBump", probeBump())
	fmt.Println("probeBumpTwice", probeBumpTwice())
	fmt.Println("probeNegBump", probeNegBump())
	fmt.Println("probeHintPanic", probeHintPanic())
	fmt.Println("probeOrder", probeOrder())
}
