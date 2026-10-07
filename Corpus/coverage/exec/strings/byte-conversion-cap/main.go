package main

// cap([]byte(s)) — the spec declares the capacity implementation-
// specific ("may be larger than the slice length", §Conversions). The
// operand s is a VARIABLE (a non-literal wire operand), the result is
// only read: gc realizes the ZERO-COPY member cap == len (the slice
// aliases the string — not "the non-escaping point": a written
// non-escaping result takes the 32-byte conversion buffer, an escaping
// one roundupsize(len); design note docs/2026-10-07_conv-cap-design.md
// §1 correction (iii)). Since R3 / b6 (2026-10-07) the machine draws
// ChoiceSite.convCap over gc's measured envelope {5, 8, 32} for this
// shape — a membership row (its observation varies with the tape, as
// the strict lane's depth guard reports) whose default-tape member is
// the pre-widening singleton 5. Born 2026-08-06 (arc-final audit F8) as
// the strict pin of the agreeing point; the narrowing it tracked is
// RETIRED.
func byteConversionCap() int {
	s := "hello"
	b := []byte(s)
	return cap(b)*10 + len(b)
}
