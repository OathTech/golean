package main

// quorum reads acks[id] and votes[id] via comma-ok; when the map is nil the
// read must yield the zero value and false. Probes the returned zero value
// (not just ok) for the map value types quorum uses, including a defined type.

type Index uint64

func nilValueCommaOk() int {
	var acks map[uint64]uint64
	var votes map[uint64]bool
	var idx map[uint64]Index
	a, oka := acks[5]  // 0, false
	b, okb := votes[5] // false, false
	c, okc := idx[5]   // Index(0), false
	r := int(a) + int(c)
	if !oka {
		r += 1
	}
	if !okb && !b {
		r += 10
	}
	if !okc {
		r += 100
	}
	return r
}
