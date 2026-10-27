package main

// Sweep S8 (lane sweep/s8-unseq, 2026-10-27): the CALL-FREE general form — two failing
// non-call occurrences with NO event between them (inventory E3 / E4 / E12(ii): the (b)
// pin of the lexical / targets-then-RHS order; the E6a trigger's general form POSED, not
// taken). Where gc's compiler-internal order is the lexical one the rows are strict and
// green (binary operands, call arguments, literal elements, a division, an assertion left
// of an index). Where gc realizes ANOTHER member the rows are born red on BUG-312's Cases
// line: a target operand's panic vs the right-hand panic (tuple and single assignment —
// gc the right-hand read's), three panicking targets (gc the middle), the map-key twin
// (gc the second target's), and an assertion RIGHT of a failing index (gc the assertion's,
// non-lexical: order.go copies the assertion early wherever it stands).

func f8() (int, int, int) { return 1, 2, 3 }

func sink(a, b int) int { return a*100 + b }

// --- green: gc realizes the lexical order ---

func twoIndexBinary() int {
	a := []int{1}
	b := []int{1, 2}
	i, j := 8, 9
	return a[i] + b[j]
}

func twoIndexArgs() int {
	a := []int{1}
	b := []int{1, 2}
	i, j := 8, 9
	return sink(a[i], b[j])
}

func twoIndexLiteral() int {
	a := []int{1}
	b := []int{1, 2}
	i, j := 8, 9
	return []int{a[i], b[j]}[0]
}

func indexLeftOfZeroDivisor() int {
	a := []int{1}
	b := []int{0}
	i := 8
	return a[i] / b[0]
}

func assertionLeftOfIndex() int {
	var iv any = "s"
	b := []int{1}
	j := 9
	return iv.(int) + b[j]
}

// --- red (BUG-312): gc realizes another member ---

func indexLeftOfAssertion() int {
	var iv any = "s"
	b := []int{1}
	j := 9
	return b[j] + iv.(int)
}

func tupleTargetPanicVsRhsPanic() int {
	xs := []int{1}
	ys := []int{1}
	zs := []int{1}
	var b int
	xs[ys[9]], b = zs[7], 2
	return b
}

func singleTargetPanicVsRhsPanic() int {
	xs := []int{1}
	ys := []int{1}
	zs := []int{1}
	xs[ys[9]] = zs[7]
	return 0
}

func threePanickingTargets() int {
	aa := [][]int{}
	cc := [][]int{{}, {}, {}}
	dd := [][]int{{}, {}, {}, {}, {}}
	aa[5][0], cc[9][0], dd[7][0] = f8()
	return 0
}

func twoPanickingMapKeys() int {
	m := map[int]int{}
	m2 := map[int]int{}
	a := []int{1}
	b := []int{1, 2}
	m[a[9]], m2[b[9]] = 1, 2
	return 0
}
