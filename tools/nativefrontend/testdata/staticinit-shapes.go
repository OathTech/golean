// staticinit-shapes.go — the BUG-061 classifier's shape table. ONE var
// spec per shape. Read by staticinit_test.go (the classifier's verdict per
// shape) and by tools/staticinitoracle via scripts/test-staticinit-oracle
// (gc's verdict per shape, recorded in staticinit-oracle.tsv: a package
// built from the preamble + the `// base` specs + that one spec, and
// whether its ..inittask record carries a function). The bases are the
// variables other shapes read; they must have no work on their own.
//
// This file is parsed, never compiled in place: the imports "errors",
// "other" and "unsafe" are taken per shape by the oracle (other =
// staticinit-other.go).
package shapes

import (
	"errors"
	"other"
	"unsafe"
)

type T struct {
	x int
	p *int
}
type T2 struct{ m map[int]int }
type T3 struct{ r []rune }
type I interface{ M() int }
type MyInt int
type R []rune

func (T) M() int { return 1 }

func one() int { return 1 }
func two() int { x := 1; return x }
func ptr() *T  { return &T{} }
func blk() int {
	{
		return 3
	}
}
func cond() int {
	if true {
		return 1
	}
	return 2
}
func condElse() int {
	if false {
		return 1
	} else {
		return 2
	}
}
func condNot() int {
	if !false {
		return 1
	}
	return 2
}
func condAnd() int {
	if true && 1 < 2 {
		return 1
	}
	return 2
}
func condVar() int {
	if one() > 0 {
		return 1
	}
	return 2
}
func condBody() int {
	if true {
		x := 1
		return x
	}
	return 2
}
func deadAfter() int  { return 1; panic("x") }
func twoReturns() int { return 1; return 2 }
func nestedIf() int {
	if true {
		if true {
			return 1
		}
	}
	return 2
}
func constDecl() int     { const c = 7; return c }
func typeDecl() int      { type t int; return 1 }
func constThenDead() int { const c = 7; return c; panic("y") }
func varDecl() int       { var v = 7; return v }
func labelled() int {
	goto L
L:
	return 1
}
func loopFalse() int {
	for false {
	}
	return 1
}
func loopInit() int {
	for x := 0; false; {
		_ = x
	}
	return 1
}
func panicOnly() int   { panic("x") }
func twoStmts() int    { _ = 1; return 1 }
func pair() (int, int) { return 1, 2 }

var (
	C       = 5               // base
	Str     = "s"             // base
	Arr     = [3]int{1, 2, 3} // base
	Sl      = []string{"a"}   // base
	St      = T{x: 1}         // base
	PtrG    = &T{}            // base
	Bytes   = []byte("abc")   // base
	IG    I = T{}             // base
	FVar    = one             // base

	Nest = []T{{x: 1}, {x: 2}}
	M    = map[int]int{1: 2}
	PM   = &map[int]int{}
	StM  = T2{m: map[int]int{}}

	Addr  = &C
	AddrF = &St.x
	AddrI = &Arr[1]
	AddrP = &PtrG.x
	Copy  = Arr
	SCopy = Str
	FCopy = other.V
	FV    = one
	FFV   = other.F
	Lit   = func() int { return 1 }
	ME    = T.M
	MV    = St.M
	Fld   = St.x
	Idx   = Arr[0]
	Bin   = C + Arr[0]
	Neg   = -Arr[0]

	Call1   = one()
	Call2   = two()
	CallP   = ptr()
	CallB   = blk()
	CallC   = cond()
	CallCE  = condElse()
	CallCN  = condNot()
	CallCA  = condAnd()
	CallCV  = condVar()
	CallCB  = condBody()
	CallDA  = deadAfter()
	CallTR  = twoReturns()
	CallNI  = nestedIf()
	CallCD  = constDecl()
	CallTD  = typeDecl()
	CallCTD = constThenDead()
	CallVD  = varDecl()
	CallLb  = labelled()
	CallLF  = loopFalse()
	CallLI  = loopInit()
	CallPO  = panicOnly()
	CallTS  = twoStmts()
	CallE   = errors.New("x")
	CallI   = IG.M()
	CallIC  = I(T{}).M()
	CallFV  = FVar()

	Conv            = MyInt(Arr[0])
	ConvC           = MyInt(C)
	ConvI         I = St
	ConvIW          = I(IG)
	ConvNil         = (*T)(nil)
	ConvAnyNested   = any(I(T{}))
	ConvAnyErrNil   = any(error(nil))
	ConvAnyIG       = any(IG)
	ConvAnyNil      = any(nil)
	BytesV          = []byte(Str)
	Runes           = []rune("abc")
	RunesN          = R("abc")
	RunesS          = T3{r: []rune("abc")}
	RunesV          = []rune(Str)
	S2              = string(Bytes)
	F2I             = float64(Arr[0])
	New             = new(int)
	Mk              = make([]int, 3)
	Len             = len(Sl)
	UP              = uintptr(unsafe.Pointer(&C))

	_   = Arr[0]
	_   = two()
	_ I = T{}

	A2, B2 = pair()
)
