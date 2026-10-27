package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: the shape's cells
// inside a GENERIC function (mono.go's instantiation: the per-iteration
// capture over a type-parameter-typed loop variable, a named-result shadow, a
// self-shadowing define, a package-level name shadowed, a type-switch guard,
// a capture by reference through a literal with a concrete-typed parameter)
// and a type parameter named `int`. Expected = gc go1.26.5.

type Number interface{ ~int | ~int64 }

func loopvarCaptureG[T Number](n T) T {
	var fs []func() T
	for i := T(0); i < n; i++ {
		fs = append(fs, func() T { return i })
	}
	return fs[0]()*100 + fs[1]()*10 + fs[2]()
}

// X1
func loopvarCapture() int { return loopvarCaptureG(3) } // 12

func resultShadowG[T Number](v T) (r T) {
	r = v
	{
		r := v * 10
		_ = r
	}
	return
}

// A26
func resultShadow() int { return resultShadowG(4) } // 4

func selfShadowG[T Number](v T) T {
	x := v
	{
		x := x + 1
		return x
	}
}

// X2
func selfShadow() int { return selfShadowG(5) } // 6

func typeparamNamedIntG[int any](x int) int { return x }

// B21
func typeparamNamedInt() string { return typeparamNamedIntG("s") + "!" } // "s!"

var gg = 3

func globalShadowG[T Number](v T) T {
	gg := v
	return gg * 2
}

// C13
func globalShadow() int { return globalShadowG(4) + gg } // 11

func tsGuardG[T any](v T) int {
	switch x := any(v).(type) {
	case int:
		return x + 1
	case string:
		return len(x)
	}
	return -1
}

// G11
func tsGuard() int { return tsGuardG(5)*10 + tsGuardG("ab") } // 62

func closureCaptureConcreteG[T Number](v T) T {
	acc := v
	add := func(d int) { acc += T(d) }
	add(1)
	add(2)
	return acc
}

// H16 control: a literal with a CONCRETE-typed parameter in a generic function lowers; the
// type-parameter-typed parameter is generics/sweep-s13-lit-param-typeparam (BUG-302, born red).
func closureCaptureConcrete() int { return closureCaptureConcreteG(10) } // 13

func main() {
	println(loopvarCapture(), resultShadow(), selfShadow(), typeparamNamedInt(), globalShadow(), tsGuard(),
		closureCaptureConcrete())
}
