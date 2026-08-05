package main

// The SAME local type declaration at TWO instantiations of the enclosing
// generic function is ordinary legal Go — gc mints distinct identities
// (main.lttTag[int], main.lttTag[string]). The un-parameterized TypeId
// made the two stencils collide at the duplicate-TypeId gate, refusing
// the whole export with a misdiagnosis ("a function-local type collides
// with another declaration" — there is ONE declaration at two
// instantiations). Arc-final audit F3 (2026-08-06), red-first.

func lttGet[T any](x T) int {
	type lttTag struct{ n int }
	_ = x
	return lttTag{1}.n
}

func localTypeTwoInstantiations() int {
	return lttGet(3) + lttGet("hi")
}
