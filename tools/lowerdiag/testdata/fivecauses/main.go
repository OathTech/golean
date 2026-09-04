// Fixture for tools/lowerdiag: EXACTLY five known blockers, one declaration
// each, beside declarations that lower. TestFixtureFiveBlockers pins the
// count; TestReportIsDeterministic renders it thrice.
package main

import (
	"strings"
	"time"
)

// 1. FR-22 (export-scoped): a package-level initializer calling an
// unmodeled stdlib function outside the H-11 allowlist.
var epoch = time.Unix(0, 0)

// 2. FR-13: an anonymous non-empty struct type.
func anonStruct() int {
	p := struct{ x, y int }{1, 2}
	return p.x + p.y
}

// 3. FR-15: complex numbers.
func complexValue() float64 {
	c := complex(1, 2)
	return real(c)
}

// 4. FR-12: range over a function iterator.
func rangeFunc(seq func(yield func(int) bool)) int {
	s := 0
	for v := range seq {
		s += v
	}
	return s
}

// 5. FR-14: a call into a stdlib package with no register row.
func packageCall() {
	time.Sleep(0)
}

// Clean declarations: these demand nothing refused.
func cleanFields(s string) int    { return len(strings.Fields(s)) }
func cleanArith(a, b int) int     { return a*b + 1 }
func cleanUsesEpoch() time.Time   { return epoch }
func clean3(m map[string]int) int { return m["a"] }
func main()                       { _ = cleanFields("a b") + cleanArith(1, 2) + clean3(nil) }
