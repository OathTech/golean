package main

// Sweep lane sweep/s10-panics (2026-10-27), shape S10 — found while probing
// G1.40 (a two-variable range over a nil *[0]T reads no element, so gc raises
// NO nil-dereference panic: zero iterations). The frontend's range emitter
// lowers a range over a ZERO-LENGTH array or pointer to array as the
// key-only static-length int range and DROPS the value variable even when
// the source declares and uses one, so the body references a local the wire
// never declares and the decoder refuses the whole wire (B6 c3) — a legal
// program (the value variable must be used, or gc rejects it as declared and
// not used) refused with status `error`. gc: every subject returns 0 (nil
// pointer: no element read; the non-nil pointer and the array value: no
// element to read), no panic.

func zeroLenPtrNilTwoVars() int {
	var p *[0]int
	n := 0
	for i, v := range p {
		n += i + v + 1
	}
	return n
}

func zeroLenPtrTwoVars() int {
	p := &[0]int{}
	n := 0
	for i, v := range p {
		n += i + v + 1
	}
	return n
}

func zeroLenPtrBlankKeyValue() int {
	var p *[0]int
	n := 0
	for _, v := range p {
		n += v + 1
	}
	return n
}

func main() {}
