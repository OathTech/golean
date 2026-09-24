package main

// Audit probes — Stage E6a attack 1: the trigger refinement's scope (event-mediated vs general).

func wit(x int) int { println("wit", x); return x }

type cell struct{ f, g int }

// (A) GENERAL-form shapes: two unordered failing occurrences with NO event between them.
func twoIdxNoEvent() int {
	a := []int{1}
	b := []int{2, 3}
	i, j := 5, 7
	return a[i] + b[j]
}

func divIdxNoEvent() int {
	x, y := 1, 0
	s := []int{1}
	i := 9
	return x/y + s[i]
}

func ptrFieldNoEvent() int {
	var p, q *cell
	return p.f + q.g
}

func assertIdxNoEvent() int {
	var iv interface{} = "s"
	s := []int{1}
	i := 9
	return iv.(int) + s[i]
}

func bug032Shape() int {
	xs := []int{1, 2}
	ys := []int{1}
	zs := []int{1}
	var b int
	xs[ys[9]], b = zs[7], 2
	return b
}

func tupleTwoFail() (int, int) {
	a := []int{1}
	b := []int{2}
	i, j := 5, 7
	var x, y int
	x, y = a[i], b[j]
	return x, y
}

// (B) EVENT-MEDIATED shapes.
func assertVsLenIdx() int { // dead-recv-len-operand's shape
	var iv interface{} = "s"
	b := make([][]int, 0)
	j := 7
	return iv.(int) + len(b[j])
}

func idxVsMakeNeg() int { // make's OWN failure vs an index panic
	a := []int{1}
	i, n := 5, -1
	return a[i] + len(make([]int, n))
}

func rightOfEvent() int {
	var iv interface{} = "s"
	b := [][]int{{1}}
	j := 5
	return len(b[j]) + iv.(int)
}

func threeFail() int { // assertion, s[i], t[k] inside make's window: three panic texts
	var iv interface{} = "s"
	s := []int{1}
	t := []int{1, 2}
	i, k := 9, 5
	return iv.(int) + s[i] + len(make([]int, t[k]))
}

func twoAssertsVsCall() int {
	var iv interface{} = "s"
	var jv interface{} = 1.5
	return iv.(int) + jv.(int) + wit(5)
}

func minShape() int {
	var iv interface{} = "s"
	t := []int{1, 2}
	k := 5
	return iv.(int) + min(t[k], 1)
}

func guardTestRegion() bool {
	a := []int{1}
	b := [][]int{{1}}
	i, j := 5, 7
	return a[i] > 0 && len(b[j]) > 0
}

func guardRegionFail() bool { // the test cannot fail; the region holds two failing across len's window
	var iv interface{} = "s"
	b := [][]int{{1}}
	j := 7
	ok := true
	return ok && iv.(int)+len(b[j]) > 0
}

func nestedWindow() int {
	var iv interface{} = "s"
	b := make([][]int, 0)
	j := 3
	return iv.(int) + len(make([]int, len(b[j])))
}

// a failing operand vs a participant that holds a NON-failing occurrence only: forced (legacy expected)
func oneFailVsLenPlain() int {
	a := []int{1}
	b := []int{2}
	i := 5
	return a[i] + len(b)
}

// two failing on the SAME side of one window: both inside make's window, no third — unordered? (b[j] vs t[k])
func twoInsideWindow() int {
	b := [][]int{{1}}
	t := []int{1, 2}
	j, k := 5, 7
	return len(make([]int, b[j][0]+t[k]))
}

// a failing target LOAD (compound) vs len's window holding a failing occurrence
func compoundLoadVsLen() int {
	x := make([]int, 1)
	b := [][]int{{1}}
	j := 5
	x[9] += len(b[j])
	return x[0]
}

// the compound op ITSELF fails (division) vs the window's failing occurrence
func compoundDivVsLen() int {
	x := 1
	y := 0
	b := [][]int{{1}}
	j := 5
	x /= len(b[j]) + y
	return x
}

func main() {}
