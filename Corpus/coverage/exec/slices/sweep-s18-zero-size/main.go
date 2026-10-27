package main

// S18 sweep — the zero-size element: gc's growslice returns {zerobase, newLen, newLen} for
// et.Size_ == 0 and the compiler never stack-buffers it, so the realized capacity is EXACTLY
// newLen on every route; the machine's slot 0 is the same (gcGrowsliceCap 0 _ = newLen) and
// the envelope stays the ordinary [newLen, max(32, 2·growth)]. Probe-verified go1.26.5, 2026-10-27.

// gc 1 = slot 0 (zero-size: cap = newLen)
func zeroNil1() int {
	var s []struct{}
	s = append(s, struct{}{})
	return cap(s)
}
