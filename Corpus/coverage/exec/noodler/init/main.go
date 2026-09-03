// noodler probes — package initialization order
// (spec#Package_initialization): dependency-driven variable
// initialization (references through function bodies count), then
// init() functions in source order.
package main

var initTrace []int

func rec(n int) int { initTrace = append(initTrace, n); return n }

// p references q (declared later) directly.
var p = q + rec(1)
var q = rec(2) * 10

// g's body references h; r calls g, so h initializes before r.
var g = func() int { return h }
var h = rec(3) + 100
var r = g() + rec(4)

// Independent declarations initialize in declaration order, blanks too.
var _ = rec(5)
var z = rec(6)

// Multi-value initialization.
func pairInit() (int, int) { rec(7); return 8, 9 }

var mx, my = pairInit()

// A function-body reference chain: a -> fa() -> b.
var a = fa()
var b = rec(10)

func fa() int { return b + 1 }

// Multiple init functions run in source order, after all variables.
var initOrder int

func init() { initOrder = initOrder*10 + 1; rec(11) }
func init() { initOrder = initOrder*10 + 2; rec(12) }

func traceDigits() int {
	d := 0
	for _, n := range initTrace {
		d = d*100 + n
	}
	return d
}

func varValues() (int, int, int, int, int) {
	return p, r, z, mx + my, a
}

func initFuncOrder() int { return initOrder }

func traceRecorded() int { return traceDigits() }

// A package-level map and slice literal referencing other globals.
var table = map[string]int{"p": p, "q": q}
var seq = []int{h, z}

func compositeGlobals() (int, int) {
	return table["p"] + table["q"], seq[0] + seq[1]
}

// A package-level method value bound at init time.
type box struct{ v int }

func (b box) get() int { return b.v }

var theBox = box{5}
var getter = theBox.get

func packageMethodValue() int {
	theBox.v = 99
	return getter()
}

func main() {}
