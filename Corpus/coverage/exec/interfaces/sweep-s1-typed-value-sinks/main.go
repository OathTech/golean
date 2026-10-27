package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// TYPED VALUES of every kind into an interface slot by ASSIGNMENT (the
// existing typed-nil rows use `var` initializers), a defined type, an
// interface-to-interface flow (the dynamic type is kept, never re-boxed), a
// value whose method set satisfies a NARROWER interface (assignment, `var`,
// argument, variadic, return, literal element, embedded interface field), the
// blank identifier's assertion and initializer, a deferred closure writing a
// named interface result, `new(expr)` over an interface operand.

type tDef int

func (d tDef) Val() int { return int(d) }

type tValer interface{ Val() int }

type tRW interface {
	R() int
	W() int
}

type tR interface{ R() int }

type tBoth struct{ n int }

func (b tBoth) R() int { return b.n }
func (b tBoth) W() int { return b.n * 2 }

type tErr struct{}

func (tErr) Error() string { return "tErr" }

type tPt struct{ X, Y int }

type tW struct{ tR }

func idAny(x any) any { return x }

func useR(r tR) int { return r.R() }

func sumR(rs ...tR) int {
	s := 0
	for _, r := range rs {
		s += r.R()
	}
	return s
}

func vals(xs ...any) []any { return xs }

func assignIntKinds() int {
	var x any
	x = int8(7)
	var y any
	y = uint64(9)
	r := 0
	switch v := x.(type) {
	case int:
		r += 1
	case int8:
		r += int(v)
	}
	switch v := y.(type) {
	case int:
		r += 100
	case uint64:
		r += int(v) * 10
	}
	return r
}

func assignFloat32() any {
	var x any
	x = float32(1.5)
	return x
}

func assignTypedNilPointer() int {
	var p *tPt
	var x any
	x = p
	r := 0
	if x != nil {
		r += 1
	}
	if v, ok := x.(*tPt); ok && v == nil {
		r += 10
	}
	return r
}

func assignSlice() int {
	var x any
	x = []int{1, 2}
	r := 0
	switch v := x.(type) {
	case []int:
		r += len(v)
	case []string:
		r += 100
	}
	var y any
	y = []string(nil)
	if v, ok := y.([]string); ok && v == nil {
		r += 10
	}
	return r
}

func assignMap() int {
	var x any
	x = map[string]int{"a": 1}
	switch v := x.(type) {
	case map[string]int:
		return v["a"]
	}
	return 0
}

func assignFunc() int {
	var x any
	x = func() int { return 3 }
	switch v := x.(type) {
	case func() int:
		return v()
	}
	return 0
}

func assignChan() int {
	c := make(chan int, 1)
	var x any
	x = c
	r := 0
	if x == c {
		r += 1
	}
	if v, ok := x.(chan int); ok {
		v <- 4
		r += <-c
	}
	return r
}

func assignStruct() int {
	var x any
	x = tPt{1, 2}
	r := 0
	if x == (tPt{1, 2}) {
		r += 1
	}
	if x != (tPt{2, 1}) {
		r += 10
	}
	return r
}

func assignArray() int {
	var x any
	x = [2]int{1, 2}
	if x == ([2]int{1, 2}) {
		return 1
	}
	return 0
}

func assignDefined() int {
	var x any
	x = tDef(3)
	r := 0
	switch x.(type) {
	case int:
		r += 1
	case tDef:
		r += 10
	}
	if v, ok := x.(tValer); ok {
		r += v.Val() * 100
	}
	return r
}

func assignIfaceToAny() int {
	var e error = tErr{}
	var x any
	x = e
	r := 0
	switch x.(type) {
	case tErr:
		r += 1
	case error:
		r += 10
	}
	if x == e {
		r += 100
	}
	return r
}

func assignNarrower() (int, bool) {
	var rw tRW = tBoth{2}
	var r tR
	r = rw
	back, ok := r.(tRW)
	if !ok {
		return -1, ok
	}
	return back.W() + r.R(), ok
}

func defineKeepsBox() int {
	var i any = int8(5)
	v := i
	switch w := v.(type) {
	case int8:
		return int(w)
	}
	return 0
}

func varNarrower() int {
	var rw tRW = tBoth{3}
	var r tR = rw
	return r.R()
}

func argDefined() any { return idAny(tDef(3)) }

func argIfaceToAny() int {
	var e error = tErr{}
	switch idAny(e).(type) {
	case tErr:
		return 1
	}
	return 0
}

func argNarrower() int {
	var rw tRW = tBoth{4}
	return useR(rw) + useR(tBoth{5})
}

func variadicNarrower() int {
	var rw tRW = tBoth{1}
	return sumR(tBoth{1}, rw, tBoth{2})
}

func variadicTyped() int {
	var p *tPt
	var e error = tErr{}
	xs := vals(p, tDef(3), e)
	r := 0
	if v, ok := xs[0].(*tPt); ok && v == nil {
		r += 1
	}
	if v, ok := xs[1].(tDef); ok {
		r += v.Val() * 10
	}
	if _, ok := xs[2].(tErr); ok {
		r += 100
	}
	return r
}

func returnNamedDefer() (r any) {
	defer func() { r = "x" }()
	return 3
}

func retR() tR {
	var rw tRW = tBoth{4}
	return rw
}

func returnNarrower() tR { return retR() }

func returnNarrowerCall() int { return retR().R() }

func returnClosure() any {
	f := func() any { return 2.5 }
	return f()
}

func embeddedIfaceLitKeyed() int {
	w := tW{tR: tBoth{5}}
	return w.R()
}

func embeddedIfaceLitPositional() int {
	w := tW{tBoth{6}}
	return w.R() + w.tR.R()
}

func sliceLitNarrower() int {
	rs := []tR{tBoth{1}, tBoth{2}}
	return rs[0].R() + rs[1].R()*10
}

func blankAssertPanic() bool {
	recovered := false
	func() {
		defer func() { recovered = recover() != nil }()
		var x any = "s"
		_ = x.(int)
	}()
	return recovered
}

func blankAssertAbort() {
	var x any = "s"
	_ = x.(int)
}

func blankVarInit() int {
	count := 0
	f := func() any {
		count++
		return 1
	}
	var _ any = f()
	var _ tR = tBoth{1}
	return count
}

func newIfaceOperand() int {
	var e error = tErr{}
	p := new(e)
	var a any = *p
	r := 0
	if _, ok := a.(tErr); ok {
		r += 1
	}
	if *p == e {
		r += 10
	}
	return r
}

func main() {
	assignIntKinds()
}
