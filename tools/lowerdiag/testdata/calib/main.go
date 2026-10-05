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
	"math"
	"math/rand"
	randv2 "math/rand/v2"
	"slices"
	"strings"
	"sync"
	"sync/atomic"
)

// ErrE (was E until 2026-10-04: dot.go's import . "math" declares math.E in the file block).
type ErrE struct{}

func (ErrE) Error() string { return "e" }

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
func isE(err error) bool { return errors.Is(err, ErrE{}) }

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

// The float-bits PRIMITIVE (tools/nativefrontend/floatbits.go, stdlib slice
// 3; folded into the Q7 fix 2026-10-04): a DIRECT call of the four math
// functions lowers (an expression statement too); defer/go and the value
// position refuse as a value-position selector; other math members stay
// unmodeled. The dot-imported bare call is in dot.go.
func fbBits(f float64) uint64       { return math.Float64bits(f) }
func fbFrom32(u uint32) float32     { return math.Float32frombits(u) }
func fbStmt(f float64)              { math.Float64bits(f) }
func fbDefer(f float64)             { defer math.Float64bits(f) }
func fbGo(f float32)                { go math.Float32bits(f) }
func fbValue() func(uint64) float64 { return math.Float64frombits }
func fbSqrt(f float64) float64      { return math.Sqrt(f) }

// fmt shim: a direct call lowers (the fmt desugar). Lowerdiag does not judge
// the verb matrix in general (disclosed in its report); this fixture holds
// only verbs whose verdict is settled, so the calibration judges it.
func sprintf(x int) string { return fmt.Sprintf("%d", x) }

// defer/go of a package-qualified stdlib member that is NOT source-through
// (lowerdiag known disagreements 1-2, 2026-10-04): the frontend lowers the
// callee as a VALUE (emit.go DeferStmt/GoStmt -> emitExpr), and a non-source
// stdlib selector in value position refuses ("stdlib-qualified selector
// fmt.Sprint / atomic.AddInt64 in value position"). The direct calls lower.
var ctr int64

func atomicCall()  { atomic.AddInt64(&ctr, 1) }
func atomicDefer() { defer atomic.AddInt64(&ctr, 1) }
func atomicGo()    { go atomic.AddInt64(&ctr, 1) }
func fmtCall()     { _ = fmt.Sprint("x") }
func fmtDefer()    { defer fmt.Sprint("x") }
func fmtGo()       { go fmt.Sprintf("%d", 1) }

// Sync-op METHOD VALUES (P-S2-6, Q-SYNCVAL; lowerdiag known disagreement 3):
// a modeled op's method value lowers over the bodied stub, promoted ones
// too; an unmodeled member's method value and every sync method EXPRESSION
// refuse.
type guarded struct{ sync.Mutex }

func syncMV(mu *sync.Mutex) func()                        { return mu.Lock }
func syncMVWg(wg *sync.WaitGroup) func()                  { return wg.Done }
func syncMVPromoted(g *guarded) func()                    { return g.Unlock }
func syncMVUnmodeled(rw *sync.RWMutex) func() sync.Locker { return rw.RLocker }
func syncMExpr() func(*sync.Mutex)                        { return (*sync.Mutex).Lock }

func entry() int { _, _ = retBox(); sortInts(nil); return fields("a b") }

func main() { entry() }
