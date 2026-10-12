package main

// The enumerators' readout-refusal fixture (the runtime lane's adversarial
// review, 2026-10-12, MEDIUM): `recoveredAsAny` returns a recovered runtime
// error as `any` — BUG-099's shape, whose observation the readout seam
// refuses by name (`readoutRefusal?`, GoLean/CLI.lean). The controls in
// scripts/check-wire-boundary run it through `coverage-observations`
// WITHOUT `--expect-status` on both engines: the refusal must be the
// ENUMERATION's (exit 1, «cannot certify the observation set», naming
// BUG-099), never a member printed under exit 0 beside `certified=`.
// `plain` is the positive control: one member, 7, on both engines.
//
// Release-readiness item 22 (2026-10-12): `retFunc`, `retBoxed` and `retAny`
// return a func value bare, in a struct field and boxed in an interface —
// each refused BY NAME at the readout (`funcObserved?`) on `native-json-run`
// and on the enumerator, and by the Go observer (`reflect.Func`); the
// observation never spells a `func` tag. The nil shapes below refuse the
// same way, on both sides.

func boom() {
	var s []int
	_ = s[3]
}

func recoveredAsAny() (out any) {
	defer func() { out = recover() }()
	boom()
	return nil
}

func plain() int { return 7 }

func add1(n int) int { return n + 1 }

type Box struct {
	F func(int) int
	N int
}

func retFunc() func(int) int { return add1 }
func retBoxed() Box          { return Box{F: add1, N: 3} }
func retAny() any            { return add1 }

// The NIL shapes (the pre-merge review's MEDIUM-1/2): refused by the
// declared result type (`funcTypeIn?`), or at an interface box by its
// dynamic type, exactly where Go's reflect refuses by static kind.
type Fn func(int) int

func retNilFunc() func(int) int           { return nil }
func retNamedFuncNilBare() Fn             { return nil }
func retNamedFuncNilBoxed() any           { var f Fn; return f }
func retNilFuncInStruct() Box             { return Box{N: 3} }
func retNilFuncInArray() [2]func(int) int { return [2]func(int) int{} }

func main() {
	println(plain())
	_ = recoveredAsAny()
	println(retFunc()(1), retBoxed().N, retAny() != nil)
	println(retNilFunc() == nil, retNamedFuncNilBare() == nil, retNamedFuncNilBoxed() != nil, retNilFuncInStruct().N, retNilFuncInArray()[0] == nil)
}
