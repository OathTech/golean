// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// Conversions of a call — BUG-047's site (the assign-site speculative emitCallNode
// guard): every conversion kind as the WHOLE right-hand side of a define/assign (bytes,
// string, rune, any, defined, pointer, float, uint8, func, bool, struct, nested,
// parenthesised, instantiated generic), the var-declaration, global-target, addressed-
// target, multi-assign, return and blank forms, in a closure, in a generic function, and
// in the argument / literal / switch-tag / if-condition positions.

package main

var cnt int

func f() int       { cnt++; return 7 }
func fs() string   { cnt++; return "ab" }
func fb() []byte   { cnt++; return []byte{65, 66} }
func fr() []rune   { cnt++; return []rune{0x41, 0x42} }
func fbyte() byte  { cnt++; return 67 }
func fbool() bool  { cnt++; return true }
func fsl() []int   { cnt++; return []int{3, 4} }
func fsv() sv      { cnt++; return sv{1, 2} }
func pf() *T       { cnt++; return &T{9} }
func ff() func() int { cnt++; return func() int { return 3 } }

type Defined int
type MyBool bool
type T struct{ n int }
type U struct{ n int }
type sv struct{ a, b int }
type nv struct{ a, b int }
type Fn func() int

var g int
var gs = []int{0, 0}

func bytesOfCall() int {
	cnt = 0
	b := []byte(fs())
	return cnt*100 + len(b)*10 + int(b[1]-65)
}

func stringOfBytesCall() int {
	cnt = 0
	s := string(fb())
	return cnt*100 + len(s)*10 + int(s[1]-65)
}

func anyOfCall() int {
	cnt = 0
	a := any(f())
	return cnt*100 + a.(int)
}

func definedOfCall() int {
	cnt = 0
	d := Defined(f())
	return cnt*100 + int(d)
}

func ptrConvOfCall() int {
	cnt = 0
	p := (*U)(pf())
	return cnt*100 + p.n
}

func returnConv() int {
	cnt = 0
	r := func() Defined { return Defined(f()) }()
	return cnt*100 + int(r)
}

func varDeclConv() int {
	cnt = 0
	var x = int(f())
	var y int = int(f())
	return cnt*100 + x + y
}

func globalTargetConv() int {
	cnt = 0
	g = int(f())
	return cnt*100 + g
}

func indexTargetConv() int {
	cnt = 0
	gs[1] = int(f())
	return cnt*100 + gs[1]
}

func twoConvMulti() int {
	cnt = 0
	x, y := int(f()), Defined(f())
	return cnt*100 + x + int(y)
}

func nestedConv() int {
	cnt = 0
	x := int(int32(f()))
	return cnt*100 + x
}

func runesOfCall() int {
	cnt = 0
	r := []rune(fs())
	return cnt*100 + len(r)*10 + int(r[1]-0x41)
}

func stringOfRunesCall() int {
	cnt = 0
	s := string(fr())
	return cnt*100 + len(s)*10 + int(s[1]-65)
}

func stringOfRuneCall() int {
	cnt = 0
	s := string(rune(f() + 60))
	return cnt*100 + int(s[0]) - 60
}

func floatOfCall() int {
	cnt = 0
	x := float64(f())
	return cnt*100 + int(x)
}

func uint8OfCall() int {
	cnt = 0
	u := uint8(f())
	return cnt*100 + int(u)
}


func funcConvOfCall() int {
	cnt = 0
	fn := Fn(ff())
	return cnt*100 + fn()
}

func boolConvOfCall() int {
	cnt = 0
	b := MyBool(fbool())
	if b {
		return cnt*100 + 1
	}
	return cnt * 100
}

func parenTypeConv() int {
	cnt = 0
	x := (int)(f())
	return cnt*100 + x
}

func convSum() int {
	cnt = 0
	x := int(f()) + int(f())
	return cnt*100 + x
}

func blankConv() int {
	cnt = 0
	_ = int(f())
	return cnt * 100
}

func stringOfByteCall() int {
	cnt = 0
	s := string(fbyte())
	return cnt*100 + int(s[0]) - 60
}

func structConvOfCall() int {
	cnt = 0
	n := nv(fsv())
	return cnt*100 + n.a*10 + n.b
}

type number interface{ ~int | ~int64 | ~float64 }

func convGeneric[T number]() T {
	x := T(f())
	return x
}

type Box[T any] struct{ v T }

func fbox() Box[int] { cnt++; return Box[int]{v: 4} }

type IntBox Box[int]

func id(x int) int { return x }

type S struct{ n int }

func closureConv() int {
	cnt = 0
	r := 0
	inner := func() {
		x := int(f())
		y := int64(f())
		r = x + int(y)
	}
	inner()
	return cnt*100 + r
}

func genericConv() int {
	cnt = 0
	a := convGeneric[int]()
	b := convGeneric[float64]()
	return cnt*100 + a + int(b)
}

func genericTypeConv() int {
	cnt = 0
	x := IntBox(fbox())
	return cnt*100 + x.v
}

func argPos() int {
	cnt = 0
	x := id(int(f()))
	return cnt*100 + x
}

func litPos() int {
	cnt = 0
	s := []int{int(f()), int(f())}
	st := S{n: int(f())}
	return cnt*100 + s[0] + s[1] + st.n
}

func switchTagPos() int {
	cnt = 0
	r := 0
	switch int64(f()) {
	case 7:
		r = 1
	default:
		r = 2
	}
	return cnt*100 + r
}

func ifCondPos() int {
	cnt = 0
	r := 0
	if int64(f()) == 7 {
		r = 1
	}
	return cnt*100 + r
}

func main() {
	bytesOfCall()
	stringOfBytesCall()
	anyOfCall()
	definedOfCall()
	ptrConvOfCall()
	returnConv()
	varDeclConv()
	globalTargetConv()
	indexTargetConv()
	twoConvMulti()
	nestedConv()
	runesOfCall()
	stringOfRunesCall()
	stringOfRuneCall()
	floatOfCall()
	uint8OfCall()
	funcConvOfCall()
	boolConvOfCall()
	parenTypeConv()
	convSum()
	blankConv()
	stringOfByteCall()
	structConvOfCall()
	closureConv()
	genericConv()
	genericTypeConv()
	argPos()
	litPos()
	switchTagPos()
	ifCondPos()
}
