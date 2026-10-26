package main

import "sub"

// Train-20 core audit, probe p11-cross-pkg-negative (2026-10-26; [USER] ruling
// relayed: a negative row — gc rejects AND the frontend refuses as a type-check
// rejection). main.C spells sub.A's fields identically, but the unexported x
// belongs to a different package: the two struct types are NOT identical
// (spec#Type_identity — non-exported field names from different packages are
// always different), so the conversion is illegal and gc rejects it with the
// substring in case.tsv; the native frontend refuses it at type-check with the
// same text (go/types). THE GUARD THIS ROW PINS: BUG-134's known limit — the
// wire's FieldDef carries no package on a field name, so the machine's
// tag-compatibility predicate (`structTagCompatible`, identical wire FieldDef
// lists) would read sub.A and main.C as compatible; the frontend's rejection
// is what keeps such a conversion off the wire. The package layout is the one
// the negative runner's module leg can build without a lookup: `require sub
// v0.0.0` + `replace sub => ./sub` (a module in sub/), which the frontend's
// case-local resolution reads as the subdirectory it is.

type C struct {
	x int
	Y int
}

func probe() int {
	pa := sub.MkA()
	pc := (*C)(pa)
	return pc.x
}

func main() { println(probe()) }
