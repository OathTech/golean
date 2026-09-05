// FR-19 pins (lane fr19-bug097, 2026-09-05; design note
// docs/2026-09-05_fr19-bug097-design.md §2.2): function-local types key
// by SCOPE ORDINAL (`main.L·1`, `main.L·2`) and DISPLAY as gc does —
// `main.L`, no scope information — so identity answers are Go's and the
// panic texts are gc's byte-exact, suffix included (`runtime/error.go`:
// equal type strings from the same package → "types from different
// scopes"; gc probe transcripts in docs/evidence/2026-09-05_fr19-bug097/).
package main

type Shadowed struct{ v int }

func (s Shadowed) Get() int { return s.v }

type box[T any] struct{ v T }

// Two functions each declare `type L int`; the closure each returns is
// the only way to name THAT function's L as an assert target from
// outside.
func mkA() (any, func(any)) { type L int; return L(1), func(x any) { _ = x.(L) } }
func mkB() (any, func(any)) { type L int; return L(2), func(x any) { _ = x.(L) } }

// gc: interface conversion: interface {} is main.L, not main.L (types from different scopes)
func localScopesPanic() int {
	va, _ := mkA()
	_, assertB := mkB()
	assertB(va)
	return 0
}

func mkA2() (any, func(any) bool) {
	type L int
	return L(1), func(x any) bool { _, ok := x.(interface{ Get() L }); return ok }
}
func mkB2() (any, func(any) bool) {
	type L int
	return L(1), func(x any) bool { _, ok := x.(interface{ Get() L }); return ok }
}

// Two anonymous interfaces `interface{ Get() L }` over two DIFFERENT
// local L's are two types (identity key `interface{Get() main.L·3}` vs
// `…·4`); a fused key would have refused the export through
// noteInterface's conflict guard (the method sets differ). Neither is
// satisfiable (a local type cannot carry methods), so both answers are
// false — the export SUCCEEDING is the observation.
func localAnonIfacesDistinct() (bool, bool) {
	va, isA := mkA2()
	vb, isB := mkB2()
	return isA(va), isB(vb)
}

// gc: interface conversion: main.L is not interface { Get() main.L }: missing method Get
func localAnonIfaceMissing() int {
	type L int
	var x any = L(1)
	_ = x.(interface{ Get() L })
	return 0
}

// assertPkgShadowed asserts to the PACKAGE-level Shadowed (the only
// scope where that name denotes it).
func assertPkgShadowed(x any) int { return x.(Shadowed).Get() }

// A local type shadowing a package-level type of the same name: the
// local `Shadowed` (key `main.Shadowed·N`) is not the package's
// `main.Shadowed`; both display `main.Shadowed`.
// gc: interface conversion: interface {} is main.Shadowed, not main.Shadowed (types from different scopes)
func localShadowPanic() int {
	type Shadowed struct{ v int }
	var x any = Shadowed{1}
	return assertPkgShadowed(x)
}

func localShadowIdentity() (bool, bool) {
	type Shadowed struct{ v int }
	var x any = Shadowed{1}
	var y any = Shadowed{1}
	_, isPkg := x.(interface{ Get() int })
	return x == y, isPkg
}

// C6 (ledger §5.1 item 1, narrowed by this lane to exactly this shape):
// a function-local type as a generic TYPE's argument — gc's observable
// name `main.box[main.score·1]` carries a compiler counter no
// source-derived key reproduces. RED BY DESIGN at frontend-export
// (mono.go's refusal names it); never a guessed numbering.
func localTypeInstantiationRefused() int {
	type score int
	b := box[score]{v: 4}
	return int(b.v)
}

func main() {
	println(localAnonIfacesDistinct())
	println(localShadowIdentity())
	println(localTypeInstantiationRefused())
	func() {
		defer func() { println(recover().(error).Error()) }()
		localScopesPanic()
	}()
	func() {
		defer func() { println(recover().(error).Error()) }()
		localAnonIfaceMissing()
	}()
	func() {
		defer func() { println(recover().(error).Error()) }()
		localShadowPanic()
	}()
}
