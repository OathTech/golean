package main

// Audit probes — the compound / deref / field LOAD left of an inline len whose operand panics (the class
// compoundLoadVsLen exposed: main realizes the LOAD's panic first, gc the len operand's), plus a few edges.

func wit(x int) int { println("wit", x); return x }

type cell struct{ f int }

func plainStoreVsLen() int { // a PLAIN store's bounds check is phase-2: [5] forced everywhere
	x := make([]int, 1)
	b := [][]int{{1}}
	j := 5
	x[9] = len(b[j])
	return x[0]
}

func derefCompoundVsLen() int { // *p += len(b[j]), p nil
	var p *int
	b := [][]int{{1}}
	j := 5
	*p += len(b[j])
	return *p
}

func fieldPtrCompoundVsLen() int { // q.f += len(b[j]), q nil
	var q *cell
	b := [][]int{{1}}
	j := 5
	q.f += len(b[j])
	return q.f
}

func derefVsLen() int { // *p + len(b[j]), p nil — a value read
	var p *int
	b := [][]int{{1}}
	j := 5
	return *p + len(b[j])
}

func fieldPtrVsLen() int {
	var q *cell
	b := [][]int{{1}}
	j := 5
	return q.f + len(b[j])
}

func idxVsLenSliceExpr() int { // s[i] + len(t[k:]) — the slice expression inside len's window
	s := []int{1}
	t := []int{1, 2}
	i, k := 9, 5
	return s[i] + len(t[k:])
}

func assertVsLenStrSlice() int { // iv.(int) + len(str[i:])
	var iv interface{} = "s"
	str := "ab"
	i := 9
	return iv.(int) + len(str[i:])
}

func assertVsCapSlice() int {
	var iv interface{} = "s"
	t := []int{1, 2}
	k := 5
	return iv.(int) + cap(t[k:])
}

func divVsLen() int { // x/y + len(b[j]) — a division by a non-constant zero left of len's window
	x, y := 1, 0
	b := [][]int{{1}}
	j := 5
	return x/y + len(b[j])
}

func shiftVsLen() int {
	x := 1
	var s int = -1
	b := [][]int{{1}}
	j := 5
	return x<<s + len(b[j])
}

func idxVsLenValid() int { // control: the len operand cannot panic — forced singleton
	s := []int{1}
	b := [][]int{{1}}
	i := 9
	return s[i] + len(b[0])
}

func compoundIdxVsLenValid() int { // control: x[9] += len(b[0]) → [9] forced
	x := make([]int, 1)
	b := [][]int{{1}}
	x[9] += len(b[0])
	return x[0]
}

func main() {}
