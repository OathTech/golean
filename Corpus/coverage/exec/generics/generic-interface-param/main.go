package main

// A generic interface instantiated at the enclosing function's type
// parameter (`gipVisitor[T]` used inside `gipApply[T ...]`): the
// interface-anchor pass used to record the origin method's
// UN-substituted signature and emit it after the mono drain with the
// substitution cleared, so the whole export died with "type parameter T
// outside an instantiation" — including the unrelated subject below
// (per-decl quarantine failure, the poisoning class the R1 rollback
// was written to prevent). Arc-final audit F5 (2026-08-06), red-first.

type gipVisitor[T any] interface {
	Visit(T) int
}

type gipStringVisitor struct{ n int }

func (v gipStringVisitor) Visit(s string) int { return v.n + len(s) }

func gipApply[T any](v gipVisitor[T], x T) int {
	return v.Visit(x)
}

func genericInterfaceParam() int {
	return gipApply[string](gipStringVisitor{10}, "abc")
}

// The unrelated subject in the same package: must not be poisoned.
func gipUnrelated() int {
	return 42
}
