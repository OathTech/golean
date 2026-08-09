// GoLean imported-goose corpus case — upstream bodies VERBATIM.
// source: testdata/examples/channel/parallel_search_replace/parallel_search_replace.go @ 3be88bbb4982f58e5813b6f0344302d5582c8e8a
// imported: 2026-08-09 by scripts/import-goose
// transform: package clause -> main; assembly order as listed; all
// GoLean-authored code sits below the harness marker.
package main


// Extracted from Gobra at
// https://github.com/viperproject/gobra/blob/b573af1cfd79d624489a5f5846d9cc0b8eb83e17/src/test/resources/regressions/examples/evaluation/parallel_search_replace.gobra/
//
// Any copyright is dedicated to the Public Domain.
// http://creativecommons.org/publicdomain/zero/1.0/

import (
	"sync"
)

func worker(c <-chan []int, wg *sync.WaitGroup, x, y int) {
	for s, ok := <-c; ok; s, ok = <-c {
		for i := 0; i != len(s); i++ {
			if s[i] == x {
				s[i] = y
			}
		}
		wg.Done()
	}
}

func SearchReplace(s []int, x, y int) {
	if len(s) == 0 {
		return
	}
	workers := 8
	workRange := 1000
	c := make(chan []int, 4)
	var wg sync.WaitGroup
	for i := 0; i != workers; i++ {
		go worker(c, &wg, x, y)
	}
	for offset := 0; offset != len(s); {
		nextOffset := offset + workRange
		if nextOffset > len(s) {
			nextOffset = len(s)
		}
		section := s[offset:nextOffset]
		wg.Add(1)
		c <- section
		offset = nextOffset
	}
	wg.Wait()
}

// --- GoLean harness ---
// One int subject per upstream boolean oracle (true -> 1, false -> 0).

// Hand-authored (zero upstream oracles): one section (len < workRange)
// through the 8-worker pool; the replaced slice is the observable. The
// workers park on the never-closed feed channel at main's exit (D6's
// unobservable leak, upstream's own shape).
func goleanSearchReplace() int {
	s := []int{1, 2, 1, 3}
	SearchReplace(s, 1, 9)
	return s[0]*1000 + s[1]*100 + s[2]*10 + s[3]
}

func main() {}
