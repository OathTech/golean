package main

// F3 witness restored (audit fix round, raft W4.0 2026-08-20).
//
// FR-13's type-argument half — an anonymous NON-EMPTY struct used as a
// type argument — used to be witnessed red by
// spec-examples-decl/compile-only-forms, whose package-level
// `var _ = satComparable[struct{ f any }]` row refused the export at
// mono.go's `anonymous non-empty struct as a type argument`. H-11's
// per-declaration quarantine turned that case green (the blank var is
// skipped, faithfully — gc evaluates the generic func value with no
// observable effect), which is correct but LOST the frontier witness.
//
// This case restores it in a form the quarantine cannot mask: the
// instantiation lives in a FUNCTION BODY, so it is emitted, not
// skipped. Red at frontend-export until structural TypeIds land
// (ledger FR-13, queue slot 13; docs/2026-08-05_generics-design.md
// §"Type args outside the supported type surface"). The empty-struct
// half of the same boundary is admitted and pinned green by
// generics/empty-struct-argument.
//
// The spec anchor is the same one the retired witness carried:
// spec#Satisfying_a_type_constraint — `struct{f any}` satisfies
// `comparable` (Go 1.20).

func asComparableArg[P comparable]() int { return 4 }

func genericAnonStructTypeArgument() int {
	return asComparableArg[struct{ f any }]()
}

func main() {
	println(genericAnonStructTypeArgument())
}
