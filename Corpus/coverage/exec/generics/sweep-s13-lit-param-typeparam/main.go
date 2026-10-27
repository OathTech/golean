package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13 — BUG-302, born red:
// a func literal whose PARAMETER has a type-parameter type, inside a generic
// function. emitFuncLit takes the literal's signature through the
// instantiation's substitution, whose parameter objects are FRESH *types.Var
// (the type changed), and registers those (B6 kind param); the body's uses
// resolve through go/types to the ORIGINAL parameter object, so emitIdent's
// localIdent mints a SECOND declaration (kind local) of the same spelling and
// position, and the decoder's B6 c4 lexical check refuses the whole wire by
// name (status error) on a legal program. A concrete-typed parameter keeps
// one object and lowers (generics/sweep-s13-contexts/lit-param-concrete).
// Expected = gc go1.26.5.

type Number interface{ ~int | ~int64 }

func closureCaptureG[T Number](v T) T {
	acc := v
	add := func(d T) { acc += d }
	add(1)
	add(2)
	return acc
}

// H16
func closureCapture() int { return closureCaptureG(10) } // 13

func dblG[T Number](v T) T {
	dbl := func(d T) T { return d * 2 }
	return dbl(v)
}

// The non-capturing form.
func litParamNoCapture() int { return dblG(10) } // 20

func main() { println(closureCapture(), litParamNoCapture()) }
