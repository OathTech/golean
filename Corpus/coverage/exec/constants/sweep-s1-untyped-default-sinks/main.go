package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// UNTYPED CONSTANTS at every assignable context whose slot is an interface:
// the constant takes its DEFAULT type (int / float64 / rune=int32 / string /
// bool) and the box carries that dynamic type — observed through the readout's
// dynamic type name, `==` against a boxed literal of the other default kind,
// and a type switch. The slots: assignment, `var` with and without a type,
// `:=`, fixed and variadic parameters (function, method, interface method,
// func value, func literal, defer, go), a defined-type and a float64 parameter,
// returns (plain, named), slice / array / map / struct literals (keyed,
// positional, nested, elided, indexed, pointer), a non-constant shift's untyped
// left operand, and a typed constant.

type sMyInt int

type sPair struct {
	A any
	B any
}

type tRecv struct{}

func (tRecv) M(x any) any { return x }

func (tRecv) V(xs ...any) any { return xs[1] }

type mIface interface{ M(x any) any }

func idAny(x any) any { return x }

func idMy(x sMyInt) any { return x }

func idF(x float64) any { return x }

func vals(xs ...any) []any { return xs }

func assignInt() any {
	var x any
	x = 1
	return x
}

func assignIntEq() int {
	var x any
	x = 1
	r := 0
	if x == 1 {
		r += 1
	}
	if x == any(1) {
		r += 10
	}
	if x == 1.0 { // the constant takes float64: never equal to the int box
		r += 100
	}
	if x != 'a' {
		r += 1000
	}
	return r
}

func assignFloat() any {
	var x any
	x = 2.5
	return x
}

func assignRune() any {
	var x any
	x = 'a'
	return x
}

func assignString() int {
	var x any
	x = "s"
	if x == "s" {
		return 1
	}
	return 0
}

func assignBool() int {
	var x any
	x = true
	switch v := x.(type) {
	case bool:
		if v {
			return 1
		}
		return 2
	}
	return 0
}

func assignShift() any {
	s := 3
	var x any
	x = 1 << s
	return x
}

func assignTypedConst() any {
	const k sMyInt = 3
	var x any
	x = k
	return x
}

func defineDefault() (any, any, any) {
	f := 1.5
	r := 'a'
	i := 1 << 40
	var a any = f
	var b any = r
	var c any = i
	return a, b, c
}

func varTypedInt() any {
	var x any = 1
	return x
}

func varTypedFloat() any {
	var x any = 2.5
	return x
}

func varTypedRune() any {
	var x any = 'b'
	return x
}

func varTypedString() any {
	var x any = "str"
	return x
}

func varTypedBool() any {
	var x any = false
	return x
}

func varUntypedThenBox() (any, any, any) {
	var i = 1 << 40
	var f = 1.5
	var r = 'a'
	var a any
	var b any
	var c any
	a = i
	b = f
	c = r
	return a, b, c
}

func argInt() any    { return idAny(1) }
func argFloat() any  { return idAny(2.5) }
func argRune() any   { return idAny('a') }
func argString() any { return idAny("s") }
func argBool() any   { return idAny(true) }

func argDefinedInt() any { return idMy(3) }

func argFloatParam() any { return idF(3) }

func argMethod() any { return tRecv{}.M(3) }

func argFuncValue() any {
	g := idAny
	return g(2.5)
}

func argIfaceMethod() any {
	var i mIface = tRecv{}
	return i.M('z')
}

func argDefer() (r any) {
	defer func(x any) { r = x }(2.5)
	return
}

func argGo() any {
	ch := make(chan any, 1)
	go func(x any) { ch <- x }(7)
	return <-ch
}

func argFuncLit() any {
	return func(x any) any { return x }(3)
}

func variadicPack() (any, any, any, any, any, bool) {
	xs := vals(1, 2.5, 'c', "s", true, nil)
	return xs[0], xs[1], xs[2], xs[3], xs[4], xs[5] == nil
}

func valsMy(xs ...sMyInt) any { return xs[0] }

func variadicDefined() any { return valsMy(1, 2) }

func variadicMethod() any { return tRecv{}.V(1, "a") }

func returnFloat() any { return 2.5 }

func returnRune() any { return 'a' }

func returnNamed() (r any) {
	r = 1.5
	return
}

func returnNamedValue() (r any) {
	return 'q'
}

func sliceLit() (any, any, any, any, any, bool) {
	xs := []any{1, 2.5, 'c', "s", true, nil}
	return xs[0], xs[1], xs[2], xs[3], xs[4], xs[5] == nil
}

func arrayLit() (any, any) {
	arr := [2]any{1, "a"}
	return arr[0], arr[1]
}

func mapLitValue() (any, any) {
	m := map[string]any{"k": 1, "f": 2.5}
	return m["k"], m["f"]
}

func structKeyed() sPair {
	return sPair{A: 1, B: "x"}
}

func structPositional() sPair {
	return sPair{2.5, 'c'}
}

func structNested() (sPair, sPair) {
	xs := []sPair{{1, "x"}}
	m := map[string]sPair{"k": {A: 2.5}}
	return xs[0], m["k"]
}

func structPointerLit() any {
	p := &sPair{A: 1}
	return p.A
}

func indexedLits() (any, any, any) {
	a := [3]any{1: "a"}
	s := []any{2: 1.5}
	return a[1], s[2], a[0]
}

func main() {
	assignInt()
}
