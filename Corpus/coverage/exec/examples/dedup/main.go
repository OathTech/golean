package main

import "fmt"

// dedupAdjacent: in-place two-pointer compaction — keeps s[i] when it
// is the first element or differs from the last kept one, and returns
// the surviving prefix s[:k]. The k == 0 disjunct short-circuits the
// s[k-1] read, so the guard never indexes out of range.
func dedupAdjacent(s []uint64) []uint64 {
	k := 0
	for i := 0; i < len(s); i++ {
		if k == 0 || s[i] != s[k-1] {
			s[k] = s[i]
			k++
		}
	}
	return s[:k]
}

func dedupFourLen(a, b, c, d uint64) uint64 {
	s := []uint64{a, b, c, d}
	r := dedupAdjacent(s)
	return uint64(len(r))
}

func dedupFourFirst(a, b, c, d uint64) uint64 {
	s := []uint64{a, b, c, d}
	r := dedupAdjacent(s)
	return r[0]
}

func dedupOne(a uint64) uint64 {
	s := []uint64{a}
	r := dedupAdjacent(s)
	return r[0]
}

func dedupEmpty() uint64 {
	s := []uint64{}
	r := dedupAdjacent(s)
	return uint64(len(r))
}

// dedupCapN: the fixed observation cap of the S3 relational harness.
// The returned arrays are `[dedupCapN]uint64`, so the harness's own
// bound is `n <= 8` — plainly visible in the source.
const dedupCapN = 8

// dedup_harness_r: the S3 RELATIONAL harness. Setup builds the family
// s[i] = seed + i/2 (integer division, so adjacent pairs repeat), the
// pre array snapshots it, the subject compacts in place, the post
// array holds the surviving prefix zero-padded, and k is its length.
func dedup_harness_r(n, seed uint64) ([dedupCapN]uint64, [dedupCapN]uint64, uint64) {
	s := make([]uint64, n)
	for i := uint64(0); i < n; i++ {
		s[i] = seed + i/2
	}
	var pre [dedupCapN]uint64
	for i := uint64(0); i < n; i++ {
		pre[i] = s[i]
	}
	r := dedupAdjacent(s)
	var post [dedupCapN]uint64
	for i := 0; i < len(r); i++ {
		post[i] = r[i]
	}
	return pre, post, uint64(len(r))
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", dedupFourLen(1, 1, 2, 3))
}
