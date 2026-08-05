package main

// cap([]byte(s)) — the spec declares the capacity implementation-
// specific ("may be larger than the slice length", §Conversions). The
// machine pins cap = len; gc's realized point depends on escape
// analysis: cap == len when the backing does not escape (this shape),
// roundupsize(len) when it does. This case version-tracks the AGREEING
// non-escaping point; the narrowing and its transfer caveat are
// recorded at the bytesFromString arm (Machine.lean) per the
// nondeterminism doctrine. Arc-final audit F8 (2026-08-06).
func byteConversionCap() int {
	s := "hello"
	b := []byte(s)
	return cap(b)*10 + len(b)
}
