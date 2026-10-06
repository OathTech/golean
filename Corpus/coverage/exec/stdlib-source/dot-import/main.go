package main

import (
	. "math"
	. "math/rand"
	. "strings"
)

// FR-36 (2026-10-06): a DOT import puts a stdlib package's members in the
// file block, so a call of one is a bare IDENTIFIER. The frontend resolves
// such an identifier through the SAME object-keyed binding as the `pkg.F`
// selector spelling (tools/nativefrontend/dotimport.go): the primitives
// lower, a quarantined member refuses BY NAME (the import form named), a
// source-through member lowers as the qualified call. Before this row the
// bare identifier lowered as a user call and the machine answered `stuck:
// GoCore function not found: Intn` — fail-noisy, cause unnamed (the 5b
// audit's F3; docs/language-coverage-ledger.md FR-36).

// intn-membership: the `[0, n)` draw as ONE choice-tape pick through the dot
// import (GoCore Stmt.randIntn / ChoiceSite.intn, window unit 5b) — the same
// admitted set {0,1,2,3,4} the selector row builtins/rand-intn/membership
// certifies; every `go run` sample lands inside (math/rand.Intn: "a
// non-negative pseudo-random number in the half-open interval [0,n)",
// deps/go/src/math/rand/rand.go:176 @ go1.26.5).
func dotIntn() int {
	return Intn(5)
}

// float-bits: the `float-bits` PRIMITIVE through the dot import (math.
// Float64bits, deps/go/src/math/unsafe.go:21 @ go1.26.5): the bit pattern
// of 1.0 is 0x3FF0000000000000; printed as the shifted high word so the
// value stays in int range on both legs. RED BY DESIGN for now (FR-36
// residual): the frontend refuses this spelling BY NAME because the
// lowering-diagnosis calibration (tools/lowerdiag cause
// dot-import-float-bits, fixture fbDot — another lane's table) pins it
// refused; the row flips to PASS with that lane's one-line cause change.
func dotFloatBits() int {
	return int(Float64bits(1.0) >> 48)
}

// strings-source-through: a dot-imported SOURCE-THROUGH member lowers from
// the pinned GOROOT text as the qualified call `strings.ToUpper` (green
// before and after FR-36; probed 2026-10-01).
func dotToUpper() int {
	return len(ToUpper("ab"))
}

// perm-quarantined: a dot-imported member the machine does NOT model
// (math/rand.Perm — every member of the two rand packages other than the
// Intn/IntN draw keeps the by-name package quarantine, randintn.go). Go runs
// it (the row's expectation is Go's: 3); the frontend refuses the
// declaration BY NAME — `package-selector call rand.Perm (package
// "math/rand" surface not modeled) — reached through a dot import` — so the
// row is RED BY DESIGN on FR-14's line (the package surface is the cause,
// the import form is now named at the point of failure).
func dotPerm() int {
	return len(Perm(3))
}

func main() {
	println(dotIntn(), dotFloatBits(), dotToUpper(), dotPerm())
}
