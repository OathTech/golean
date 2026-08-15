package main

import "fmt"

// rle: run-length encode s into two parallel slices (runValues,
// runCounts), built with append — walk s, extending the current run
// while the value repeats, starting a new run otherwise. INTERNAL
// subject: it returns slices, so it is never a corpus subject directly;
// the scalar drivers and the fixed-cap harness below observe it.
func rle(s []uint64) ([]uint64, []uint64) {
	runVals := []uint64{}
	runCounts := []uint64{}
	for i := 0; i < len(s); i++ {
		k := len(runVals)
		extended := false
		if k > 0 {
			if runVals[k-1] == s[i] {
				runCounts[k-1]++
				extended = true
			}
		}
		if !extended {
			runVals = append(runVals, s[i])
			runCounts = append(runCounts, 1)
		}
	}
	return runVals, runCounts
}

// rleFourCount: number of runs in the four-element input.
func rleFourCount(a, b, c, d uint64) uint64 {
	vals, _ := rle([]uint64{a, b, c, d})
	return uint64(len(vals))
}

// rleFourFirst: the first run's value and count in the four-element
// input.
func rleFourFirst(a, b, c, d uint64) (uint64, uint64) {
	vals, counts := rle([]uint64{a, b, c, d})
	return vals[0], counts[0]
}

func rleOne(a uint64) (uint64, uint64) {
	vals, counts := rle([]uint64{a})
	return vals[0], counts[0]
}

func rleEmpty() uint64 {
	vals, _ := rle([]uint64{})
	return uint64(len(vals))
}

// rleCapN: the fixed observation cap of the S3 relational harness. The
// returned arrays are `[rleCapN]uint64`, so the harness's own bound is
// `n <= 8` — plainly visible in the source, and the Lean headline
// carries it as a hypothesis.
const rleCapN = 8

// rle_harness_r: the S3 RELATIONAL harness (gallery campaign G1,
// 2026-08-15). Setup builds the family s[i] = seed + i/3, so runs of
// length up to 3 appear; the harness returns the PRE-STATE alongside
// the encoded (runVals, runCounts) — all as fixed-cap arrays, the
// pass-by-value fragment's unbounded-data workaround — plus the run
// count k, so the Lean postcondition relates the returned data
// DIRECTLY, with no family function re-describing the setup. Real Go,
// ghost ladder rung 0.
func rle_harness_r(n, seed uint64) ([rleCapN]uint64, [rleCapN]uint64, [rleCapN]uint64, uint64) {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i/3
	}
	var pre [rleCapN]uint64
	for i := uint64(0); i < n; i++ {
		pre[i] = s[i]
	}
	vals, counts := rle(s)
	var runVals [rleCapN]uint64
	var runCounts [rleCapN]uint64
	for i := 0; i < len(vals); i++ {
		runVals[i] = vals[i]
		runCounts[i] = counts[i]
	}
	return pre, runVals, runCounts, uint64(len(vals))
}

func main() {
	v, c := rleFourFirst(7, 7, 3, 3)
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		v, c,
	)
}
