// Lane frontend/fix-paren-forms-1105 (2026-11-05), the fix of BUG-420 (the
// parenthesised blank target crashed the frontend) and BUG-421 (the
// parenthesised range target refused): the blank spelled `(_)` on every
// assignment route the S28 sweep's Cases rows do not reach — the comma-ok
// map read, receive and assertion, the select clause (pair and blank-only),
// a lifted closure body, the receive statement, a generic body, and the
// assign-form range's key. go/types reads every target through ast.Unparen
// (lhsVar); so does the emitter now. Expected = gc go1.26.5.

package main

var n int

func bump() int { n++; return n }

func pair[T any](v T) (T, T) { return v, v }

func parenBlankCommaOkMap() int {
	m := map[string]int{"a": 1}
	var ok bool
	(_), ok = m["a"]
	if ok {
		return 1
	}
	return 0
}

func parenBlankCommaOkRecv() int {
	ch := make(chan int, 1)
	ch <- 7
	var v int
	(v), (_) = <-ch
	return v // 7
}

func parenBlankCommaOkAssert() int {
	var i any = 3
	var t int
	(t), (_) = i.(int)
	return t // 3
}

func parenBlankSelectPair() int {
	ch := make(chan int, 1)
	ch <- 9
	var v int
	select {
	case (v), (_) = <-ch:
		return v // 9
	}
}

func parenBlankSelectOnly() int {
	ch := make(chan int, 1)
	ch <- 2
	select {
	case (_) = <-ch:
		return len(ch) // 0
	}
}

func parenBlankClosure() int {
	n = 0
	f := func() { (_) = bump(); (_) = (bump()) }
	f()
	return n // 2
}

func parenBlankRecvStmt() int {
	ch := make(chan int, 1)
	ch <- 3
	(_) = <-ch
	return len(ch) // 0
}

func genBlank[T any](v T) T {
	(_) = v
	(_), (_) = pair(v)
	var a, b T
	(a), (b) = pair(v)
	_ = a
	return b
}

func parenBlankGeneric() int { return genBlank(5) + len(genBlank("st")) } // 7

func parenBlankRangeKey() int {
	s := []int{10, 20}
	var v, sum int
	for (_), (v) = range s {
		sum += v
	}
	return sum // 30
}

func parenBlankRangeOnly() int {
	s := []int{1, 2, 3}
	c := 0
	for (_) = range s {
		c++
	}
	return c // 3
}

func main() {
	println("parenBlankCommaOkMap", parenBlankCommaOkMap())
	println("parenBlankCommaOkRecv", parenBlankCommaOkRecv())
	println("parenBlankCommaOkAssert", parenBlankCommaOkAssert())
	println("parenBlankSelectPair", parenBlankSelectPair())
	println("parenBlankSelectOnly", parenBlankSelectOnly())
	println("parenBlankClosure", parenBlankClosure())
	println("parenBlankRecvStmt", parenBlankRecvStmt())
	println("parenBlankGeneric", parenBlankGeneric())
	println("parenBlankRangeKey", parenBlankRangeKey())
	println("parenBlankRangeOnly", parenBlankRangeOnly())
}
