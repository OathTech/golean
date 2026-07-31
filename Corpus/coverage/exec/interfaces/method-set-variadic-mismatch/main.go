package main

// Interface satisfaction compares VARIADIC-NESS, not merely the parameter
// TYPES. In Go, `M(xs ...int) int` and `M(xs []int) int` are different
// method signatures, so a type declaring one does not implement an
// interface requiring the other — in either direction (pre-merge audit
// 2026-07-31, finding 0: the machine compared only the canonicalized
// param/result type lists, so the comma-ok assert answered `true` and the
// panicking assert ran an ill-typed dispatch where Go aborts).

type variadicReqIface interface{ M(xs ...int) int }

type sliceImpl struct{ v int }

func (t sliceImpl) M(xs []int) int { return t.v + len(xs) }

// Requirement VARIADIC, implementation a plain slice: not satisfied.
func variadicReqSliceImpl() int {
	var x any = sliceImpl{v: 7}
	_, ok := x.(variadicReqIface)
	if ok {
		return 1
	}
	return 0
}

// The panicking form of the same pair — Go aborts with `missing method M`.
func variadicReqSliceImplPanic() int {
	var x any = sliceImpl{v: 7}
	j := x.(variadicReqIface)
	return j.M(1, 2, 3)
}

type sliceReqIface interface{ M(xs []int) int }

type variadicImpl struct{ v int }

func (t variadicImpl) M(xs ...int) int { return t.v + len(xs) }

// The REVERSE direction: requirement a plain slice, implementation variadic.
func sliceReqVariadicImpl() int {
	var x any = variadicImpl{v: 7}
	_, ok := x.(sliceReqIface)
	if ok {
		return 1
	}
	return 0
}

// The POSITIVE pair — variadic requirement met by a variadic method — which
// must keep satisfying and dispatching (the fix must not fail closed here).
type variadicOkIface interface{ M(xs ...int) int }

type variadicOk struct{ v int }

func (t variadicOk) M(xs ...int) int { return t.v + len(xs) }

func variadicReqVariadicImpl() int {
	var x any = variadicOk{v: 7}
	j, ok := x.(variadicOkIface)
	if !ok {
		return 0
	}
	return j.M(1, 2, 3)
}

// Variadic-ness must not be the ONLY thing compared: a variadic pair whose
// element types differ is still unsatisfied.
type variadicElemIface interface{ M(xs ...int8) int }

func variadicElemMismatch() int {
	var x any = variadicOk{v: 7}
	_, ok := x.(variadicElemIface)
	if ok {
		return 1
	}
	return 0
}
