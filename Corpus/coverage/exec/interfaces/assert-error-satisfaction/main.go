package main

// Interface satisfaction must be decided by the interface's DECLARED method
// set, not by which methods happen to be CALLED elsewhere in the package
// (pre-merge audit 2026-07-31, finding 0: `_, ok := x.(error)` was
// unconditionally true whenever no `.Error()` call site existed).

type myErr struct{ code int }

func (e myErr) Error() string { return "boom" }

// A negative assert to the predeclared `error` in a package that NEVER calls
// Error(): Go says false.
func assertErrorNoCall() int {
	var x any = 3
	_, ok := x.(error)
	if ok {
		return 1
	}
	return 0
}

// The same, in a package that DECLARES an error implementation but still never
// calls Error(): declaring is not calling, and neither one is the requirement.
func assertErrorDeclaredNotCalled() int {
	var x any = "not an error"
	_, ok := x.(error)
	if ok {
		return 1
	}
	return 0
}

// The positive direction: a real implementation satisfies `error`.
func assertErrorPositive() int {
	var x any = myErr{code: 7}
	_, ok := x.(error)
	if ok {
		return 1
	}
	return 0
}

// The recover-discrimination idiom (`if err, ok := r.(error); ok`), the shape
// the north-star target uses and the one that by construction never calls
// Error(): it must still discriminate.
func classifyPayload(r any) int {
	if _, ok := r.(error); ok {
		return 1
	}
	return 2
}

func assertErrorClassify() int {
	return classifyPayload("plain string")*10 + classifyPayload(myErr{code: 1})
}
