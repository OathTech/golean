package main

// Round-4 pins (BUG-034): the comma-ok forms `v, ok = m[k]` and
// `v, ok = x.(T)` are two-phase assignments like any other — target
// operands in phase 1 (checks deferred), source evaluated, stores
// left-to-right in phase 2. The eager stmtPlan path fires the second
// target's oob/nil-field check before the first store lands.

func coRecover(fn func()) (hit int) {
	defer func() {
		if recover() != nil {
			hit = 1
		}
	}()
	fn()
	return 0
}

func commaOkMapOob() int {
	m := map[int]int{1: 7}
	xs := []int{0}
	bs := []bool{false}
	hit := coRecover(func() { xs[0], bs[9] = m[1] })
	return hit*1000 + xs[0]
}

type coT struct{ b bool }

func commaOkAssertNilField() int {
	var iv interface{} = 5
	xs := []int{0}
	var p *coT
	hit := coRecover(func() { xs[0], p.b = iv.(int) })
	return hit*1000 + xs[0]
}

// GUARD (stays green): the phase-1 operand-capture half — bs[i] reads
// the pre-store i.
func commaOkDepIndex() int {
	m := map[int]int{1: 2}
	i := 0
	bs := []bool{false, false, false}
	i, bs[i] = m[1]
	n := i * 100
	for j := range bs {
		if bs[j] {
			n += j + 1
		}
	}
	return n
}

func main() {
	commaOkMapOob()
}
