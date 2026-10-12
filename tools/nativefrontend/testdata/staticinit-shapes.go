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

// g is a bool the writer cannot decide (writer.staticBool: 0).
func g() bool { return true }

func condFalseAndG() int {
	if false && g() {
		return 1
	}
	return 2
}
func condTrueOrG() int {
	if true || g() {
		return 1
	}
	return 2
}
func condTrueAndFalseAndG() int {
	if true && false && g() {
		return 1
	}
	return 2
}
func condGAndFalse() int {
	if g() && false {
		return 1
	}
	return 2
}
func condGOrTrue() int {
	if g() || true {
		return 1
	}
	return 2
}
func condFalseOrG() int {
	if false || g() {
		return 1
	}
	return 2
}
func bareNamed() (x int) { return }

//go:noinline
func noInline() int { return 1 }

func mkClosure(x int) func() int { return func() int { return x } }

func id[T any](x T) T { return x }

func forGAndFalse() int {
	for g() && false {
	}
	return 1
}
func condParenOrTrue() int {
	if (g() || false) || true {
		return 1
	}
	return 2
}
func condGAndFalseElse() int {
	if g() && false {
		return 1
	} else {
		return 2
	}
}

// INIT SHAPES: a function named init<Key> with no parameters is an init
// body shape — the oracle builds it renamed to `init`, the unit test judges
// it with initBodyWork; neither includes it in any other package.
func initEmpty()     {}
func initConstDecl() { const c = 1 }
func initTypeDecl()  { type t int }
func initEmptyBlock() {
	{
	}
}
func initIfFalse() {
	if false {
		g()
	}
}
func initForFalse() {
	for false {
		g()
	}
}
func initBlank()   { _ = 1 }
func initVarDecl() { var x int; _ = x }
func initCall()    { g() }
func initIfGAndFalse() {
	if g() && false {
	}
}
func initReturn()          { return }
func initDeadAfterReturn() { return; g() }
func initIfTrueCall() {
	if true {
		g()
	}
}

var (
	C              = 5               // base
	Str            = "s"             // base
	Arr            = [3]int{1, 2, 3} // base
	Sl             = []string{"a"}   // base
	St             = T{x: 1}         // base
	PtrG           = &T{}            // base
	Bytes          = []byte("abc")   // base
	IG    I        = T{}             // base
	FVar           = one             // base
	InlV           = one()           // base
	Ch    chan int                   // base

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
	SlAny           = []any{IG}

	CallFG  = condFalseAndG()
	CallTG  = condTrueOrG()
	CallTFG = condTrueAndFalseAndG()
	CallGF  = condGAndFalse()
	CallGT  = condGOrTrue()
	CallFOG = condFalseOrG()
	CallBN  = bareNamed()
	CallNoI = noInline()
	CopyInl = InlV
	CallClo = mkClosure(1)
	CallFGF = forGAndFalse()
	CallPOT = condParenOrTrue()
	CallGFE = condGAndFalseElse()
	SlCh    = []<-chan int{Ch}

	_   = Arr[0]
	_   = two()
	_ I = T{}
	_   = St.M
	_   = func() int { return 1 }
	_   = func() int { return 1 }()
	_   = make(chan int)
	_   = make(map[int]int)
	_   = make(chan int, 0)
	_   = make(chan int, 2)
	_   = make([]int, 0)
	_   = (*T)(PtrG) == nil
	_   = len([]*T{PtrG})
	_   = id[int] == nil
	_   = len([]func(int) int{id[int]})
	_   = func() int { return two() }()
	_   = func() {}
	_   = []func(){func() {}}

	A2, B2 = pair()
)
