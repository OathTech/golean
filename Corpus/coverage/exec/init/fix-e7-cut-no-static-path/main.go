package main

// Lane frontend/fix-e7-cut-1107 (2026-11-07): the CONTROLS of init/fix-e7-cut-partial-static — a hidden
// read (through an interface method) of a package variable whose initializer has NO static path at the
// top level (a call to a multi-statement body, a map literal, arithmetic, an index or field read, a tuple,
// `new`, a slice expression, `[]byte` of a variable, a same-kind float conversion): StaticAssign returns
// false for the shape, gc assigns the whole value at its InitOrder position, the machine too, and the
// hidden read finds the same zero on both sides. The E7 detector lets each lower; green on both sides.

type S struct{ a, b int }

var sink int

func g() int {
	for i := 0; i < 3; i++ {
		sink += i
	}
	return sink
}

func pair() (int, int) { return 4, 5 }

type cI interface{ m() int }
type cT struct{}

func (cT) m() int { return yc }

var xc = cI(cT{}).m()
var yc = g()

func ctlCall() int { return xc*100 + yc }

type mI interface{ m() int }
type mT struct{}

func (mT) m() int { return len(ym) }

var xm = mI(mT{}).m()
var ym = map[int]int{1: g()}

func ctlMap() int { return xm*100 + len(ym) }

type aI interface{ m() int }
type aT struct{}

func (aT) m() int { return ya }

var xa = aI(aT{}).m()
var yac = 4
var ya = yac + g()

func ctlArith() int { return xa*100 + ya }

type iI interface{ m() int }
type iT struct{}

func (iT) m() int { return yi }

var xi = iI(iT{}).m()
var arr = [2]int{7, 8}
var yi = arr[0]

func ctlIndex() int { return xi*100 + yi }

type fI interface{ m() int }
type fT struct{}

func (fT) m() int { return yf }

var xf = fI(fT{}).m()
var sf = S{a: 1, b: 2}
var yf = sf.a

func ctlField() int { return xf*100 + yf }

type tI interface{ m() int }
type tT struct{}

func (tT) m() int { return yt + zt }

var xt = tI(tT{}).m()
var yt, zt = pair()

func ctlTuple() int { return xt*100 + yt + zt }

type nI interface{ m() int }
type nT struct{}

func (nT) m() int {
	if yn == nil {
		return 7
	}
	return 1
}

var xn = nI(nT{}).m()
var yn = new(S)

func ctlNew() int { return xn*100 + yn.a }

type sI interface{ m() int }
type sT struct{}

func (sT) m() int { return len(ys) }

var xs = sI(sT{}).m()
var ysb = []int{1, 2, 3}
var ys = ysb[0:2]

func ctlSliceExpr() int { return xs*100 + len(ys) }

type bI interface{ m() int }
type bT struct{}

func (bT) m() int { return len(yb) }

var xb = bI(bT{}).m()
var sv = "ab"
var yb = []byte(sv)

func ctlBytesVar() int { return xb*100 + len(yb) }

type dI interface{ m() int }
type dT struct{}

func (dT) m() int { return int(yd) }

var xd = dI(dT{}).m()
var fv = 2.5
var yd = float64(fv)

func ctlConvFloat() int { return xd*100 + int(yd) }

func main() {
	println(ctlCall(), ctlMap(), ctlArith(), ctlIndex(), ctlField(), ctlTuple(), ctlNew(), ctlSliceExpr(), ctlBytesVar(), ctlConvFloat())
}
