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

// 3. strings.IndexRune's body uses a `goto next` whose target label is
//    lowered by the frontend's goto restructuring — the reached shape
//    hits FR-11's fresh-cell-per-execution refusal (`goto target label
//    next…`), so IndexRune quarantines by name. Remedy: FR-11's goto
//    lowering (a LANGUAGE frontier, not a library one).
// 4. internal/strconv's float path (`ftoa.go`, `atof.go`) reaches the
//    four `unsafe.Pointer` float-bits casts in deps.go — strconv.
//    FormatFloat/ParseFloat/AppendFloat quarantine by name. Remedy: the
//    slice-2 overlay onto the machine's FloatBits (memo §2.3.2).

import (
	"math/bits"
	"strconv"
	"strings"
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

// gc: 3 (the byte offset of the rune); machine: refuses in strings.IndexRune
// (goto shape, FR-11).
func indexRuneGoto() int { return strings.IndexRune("ab\u00e9d", 'd') }

// gc: "1.5"; machine: refuses on internal/strconv's float-bits casts
// (unsafe.Pointer, deps.go).
func formatFloatUnsafe() string { return strconv.FormatFloat(1.5, 'g', -1, 64) }

func main() {
	println(atoiErrorPathClone())
	println(div64OverflowValue())
	println(indexRuneGoto())
	println(formatFloatUnsafe())
}
