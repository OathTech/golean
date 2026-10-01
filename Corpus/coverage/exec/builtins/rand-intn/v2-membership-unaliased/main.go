package main

// The UNALIASED spelling of v2-membership: `import "math/rand/v2"` binds the
// package clause's name `rand`. This row pins the oracle harness's
// assumed-name rule (tools/coverageharness/main.go `assumedImportName`,
// goimports' rule: a major-version last element names the previous element)
// — before that fix the harness assumed `v2`, pruned the import as unused,
// and the oracle build failed `undefined: rand` (audit F4,
// docs/2026-10-01_intn-pick-audit.md). The sibling v2-membership keeps the
// explicit alias, so both spellings stay covered.
import "math/rand/v2"

// The same site through the v2 callee (math/rand/v2.IntN, v2/rand.go:189 @
// go1.26.5 — "a non-negative pseudo-random number in the half-open interval
// [0,n)"): bound 3, admitted set {0,1,2}.
func drawThree() int {
	return rand.IntN(3)
}

func main() {
	println(drawThree())
}
