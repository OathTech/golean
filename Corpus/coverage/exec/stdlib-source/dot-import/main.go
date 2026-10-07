package main

import (
	. "math"
	. "math/rand"
	"os"
	. "os"
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
// value stays in int range on both legs. (Born red on 2026-10-06's first
// landing attempt while the lowering-diagnosis calibration — then another
// lane's table — pinned this spelling refused; the cause retired the same
// day, and the row is a PASS.)
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

// var-args (FR-37, 2026-10-07): a dot-imported package-level VARIABLE of a
// non-source stdlib package (os.Args, deps/go/src/os/proc.go:16 @ go1.26.5:
// "Args hold the command-line arguments, starting with the program name" —
// so len >= 1 under `go run`; the row's expectation is Go's: 1). The
// frontend refuses the declaration BY NAME — `imported package-level
// variable os.Args has no seeded cell — reached through a dot import` —
// RED BY DESIGN on FR-14's line (package "os" is outside the modeled
// surface; the qualified `os.Args` refuses there too). Before FR-37 the
// bare identifier reached the wire as `{"expr":"ident","local":0,
// "name":"Args"}` and the DECODER refused the WHOLE wire unnamed (B6 c3) —
// every sibling row in this file, the three PASS rows included, went red
// with it.
func dotArgs() int {
	if len(Args) >= 1 {
		return 1
	}
	return 0
}

// var-masking-sibling (FR-37): a QUALIFIED quarantined call in the same
// program as the dot-imported variable. Go runs it (the variable is unset:
// 0); the frontend refuses it by its OWN name — `package-selector call
// os.Getenv (package "os" surface not modeled)` — RED BY DESIGN on FR-14's
// line. Before FR-37 this refusal was MASKED: the whole-wire decode failure
// above reported the unnamed B6 c3 cause instead.
func qualifiedGetenv() int {
	return len(os.Getenv("GOLEAN_FR37_UNSET"))
}

func main() {
	println(dotIntn(), dotFloatBits(), dotToUpper(), dotPerm(), dotArgs(), qualifiedGetenv())
}
