package main

// BORN-RED FRONTIER ROWS of stdlib source-through slice 1 (2026-09-03;
// [USER] direction 3, relayed: every detected gap is rowed). Each row is a
// program gc runs fine and the machine REFUSES BY NAME at a library site
// the slice cannot lower yet; the refusal text names the site and the
// planned remedy. Expected status is gc's (ok); the baseline records the
// refusal. A row turning green is the remedy landing (a FAIL->PASS flip,
// free); a row turning into a wrong answer is a BUG.
//
// 1. internal/stringslite.Clone's `unsafe.String` — reached by EVERY
//    strconv Parse* error path through syntaxError/rangeError (the memo's
//    §1.3 impurity census listed strings/builder.go, errors/join.go,
//    internal/strconv/deps.go and slices.overlaps, NOT this site). Remedy:
//    the slice-2 overlay (`Clone` = string(b) — the unsafe.String is an
//    allocation-avoidance idiom; the bytes are equal). Until then the
//    ParseUint SHIM is retained (it constructs the real *NumError without
//    routing through Clone); Atoi/ParseInt/ParseFloat error paths refuse
//    at run time with the Clone stub's reason.
// 2. math/bits' runtime-linknamed error VALUES (`overflowError` /
//    `divideError` = runtime.overflowError/divideError) — reached by
//    bits.Div64's panic path; poisoned by the linkname rule (a read
//    refuses, never a nil error). Remedy: a spec'd primitive or overlay
//    mapping the two values onto the machine's own division/overflow
//    panics (they ARE the language's panics — memo §1.3 Finding 1).

import (
	"math/bits"
	"strconv"
)

// gc: -1 (Atoi("x") fails with *NumError); machine: refuses in
// internal/stringslite.Clone (unsafe.String).
func atoiErrorPathClone() int {
	n, err := strconv.Atoi("x")
	if err != nil {
		return -1
	}
	return n
}

// gc: panics "runtime error: integer overflow" (bits.Div64 with hi >= y
// panics with runtime.overflowError); machine: refuses reading the
// poisoned linknamed variable.
func div64OverflowValue() uint64 {
	q, _ := bits.Div64(5, 0, 3)
	return q
}

func main() {
	println(atoiErrorPathClone())
	println(div64OverflowValue())
}
