// SAME-GOROUTINE control for the E9 intervening-insert finding (GoLean
// Tier-5 slice, 2026-09-02): the ranging goroutine ITSELF deletes the
// current key, inserts `fresh` fresh keys, and re-inserts the key — the
// `maps/delete-readd-during-range` idiom plus intervening inserts.
// Observable: how many times the first-produced key k0 is produced
// (1 = skipped after re-creation, 2 = produced again). Recorded because
// ledger L-012's oracle data ("gc never re-produces — 400/400 incl.
// forced growth") was gathered without small intervening inserts.
package main

import (
	"fmt"
	"os"
	"runtime"
	"strconv"
)

func trial(size, fresh int) int {
	m := make(map[int]int)
	for i := 1; i <= size; i++ {
		m[i] = i
	}
	kcount := 0
	first := true
	k0 := 0
	next := 1000000
	for k := range m {
		if first {
			first = false
			k0 = k
			kcount++
			delete(m, k)
			for i := 0; i < fresh; i++ {
				next++
				m[next] = next
			}
			m[k] = k + 10
			continue
		}
		if k == k0 {
			kcount++
		}
	}
	return kcount
}

func main() {
	trials, _ := strconv.Atoi(os.Args[1])
	size, _ := strconv.Atoi(os.Args[2])
	fresh, _ := strconv.Atoi(os.Args[3])
	counts := map[int]int{}
	for i := 0; i < trials; i++ {
		counts[trial(size, fresh)]++
	}
	fmt.Printf("same-goroutine GOMAXPROCS=%d size=%d fresh=%d trials=%d -> n=1:%d n=2:%d other:%d\n",
		runtime.GOMAXPROCS(0), size, fresh, trials, counts[1], counts[2], trials-counts[1]-counts[2])
}
