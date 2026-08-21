package main

// BUG-067 guardrails: spec#Type_identity distinguishes `func(...int) int`
// from `func([]int) int`, but the wire's func TYPE nodes dropped the
// variadic bit — both assertions below carried byte-identical targetTypes,
// so the machine answered `true` for both where gc answers `false`/`true`
// (census 2026-08-21 §10 H-d, the confirmed witness). `Func` declarations
// and interface-method requirements always carried the bit (pre-merge
// audit 2026-07-31 finding 0); the TYPE nodes are what these rows pin.

func variadicFn(xs ...int) int { return len(xs) }
func sliceFn(xs []int) int     { return len(xs) }

func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

// gc: okSlice=false (different type identity), okVar=true.
func mismatchVariadicAtSlice() int {
	var i any = variadicFn
	_, okSlice := i.(func([]int) int)
	_, okVar := i.(func(...int) int)
	return b2i(okSlice)*10 + b2i(okVar)
}

// The mirror direction: a boxed non-variadic func asserted at the
// variadic type. gc: okVar=false, okSlice=true.
func mismatchSliceAtVariadic() int {
	var i any = sliceFn
	_, okVar := i.(func(...int) int)
	_, okSlice := i.(func([]int) int)
	return b2i(okVar)*10 + b2i(okSlice)
}

// The PANIC direction (holes-arc audit fix round 2026-08-21, finding
// F3): a single-result assertion at the wrong func type must panic. This
// is the sharper witness of the same hole — pre-fix the machine did not
// merely answer the wrong BOOLEAN, it took the wrong CONTROL PATH and
// returned normally with status `ok` where gc panics (measured: pre-fix
// `{"status":"ok","values":[0]}`; gc `panic: interface conversion: ...`).
//
// It also pins the RENDER: the panic message names the dynamic type with
// the variadic spelling `func(...int) int`, which only exists because
// `goTypeNameForMessageFuel` prints the last parameter of a variadic
// signature as `...E`. The row is byte-exact against gc's message, so
// dropping the bit from the render — not just from identity — is red.
func assertVariadicAtSlicePanic() int {
	var i any = variadicFn
	_ = i.(func([]int) int)
	return 0
}

// Green control: asserting at exactly the boxed type answers true, and
// the asserted value still calls.
func matchRightTypes() int {
	var iv any = variadicFn
	var is any = sliceFn
	fv, okV := iv.(func(...int) int)
	fs, okS := is.(func([]int) int)
	if !okV || !okS {
		return -1
	}
	return fv(1, 2, 3)*10 + fs([]int{4})
}
