// Calibration fixture for tools/lowerdiag (TestCalibrationAgainstWire): the
// REAL frontend emits a wire for this program and the test asserts that the
// static verdict of every user declaration agrees with the wire's quarantine
// set — including the FR-7 RETURN case (lowers: the emitter destructures
// `return two()` with an explicit box; the audit's phantom row) and three
// cases the first cut missed (slices.Sort at []string, defer of an
// intercepted member, errors.Is through a source-through package).
package main

import (
	"errors"
	"fmt"
	"math/rand"
	randv2 "math/rand/v2"
	"slices"
	"strings"
)

type E struct{}

func (E) Error() string { return "e" }

func two() (int, string) { return 1, "a" }

// FR-7's shape on the RETURN path: lowers (assign/value-spec paths refuse).
func retBox() (any, string) { return two() }

// FR-7's real shape: an interface TARGET of a multi-value ASSIGN refuses.
func assignBox() (any, string) {
	var x any
	var s string
	x, s = two()
	return x, s
}

// slices.Sort is the real source-through generic at every ordered kind
// (memo §3 row M, 2026-09-04): both lower.
func sortStrings(s []string) { slices.Sort(s) }
func sortInts(s []int)       { slices.Sort(s) }

// defer of slices.Sort: the intercept table is empty since row M, so the
// deferred FUNCTION VALUE is the real generic and lowers.
func deferSort(s []int) { defer slices.Sort(s) }

// errors.Is reaches internal/reflectlite (register: refuses by name).
func isE(err error) bool { return errors.Is(err, E{}) }

// source-through member that lowers.
func fields(s string) int { return len(strings.Fields(s)) }

// The rand-intn PRIMITIVE (tools/nativefrontend/randintn.go, window unit 5b;
// route-A review Q7, 2026-10-04): a DIRECT call of the package-level
// math/rand.Intn / math/rand/v2.IntN lowers to the `rand-intn` node, so both
// declarations LOWER; the method form, defer of the function and every other
// member of the package stay refused.
func drawIntn(n int) int          { return rand.Intn(n) }
func drawIntNv2(n int) int        { return randv2.IntN(n) }
func drawInt63n() int64           { return rand.Int63n(5) }
func deferIntn()                  { defer rand.Intn(5) }
func drawMethod(r *rand.Rand) int { return r.Intn(5) }

// fmt shim: the verb matrix is NOT judged statically (disclosed, not asserted).
func sprintf(x int) string { return fmt.Sprintf("%d", x) }

func entry() int { _, _ = retBox(); sortInts(nil); return fields("a b") }

func main() { entry() }
