// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). The comma-ok special forms with
// a PARENTHESISED right-hand side — `v, ok := (m[k])`, `(x.(T))`, `(<-ch)` — at the
// define, assignment and var sinks (gc accepts them: go/types reads the two-value form
// through the parentheses); expected = gc go1.26.5.

package main

func parenCommaOkRhsDefine() int {
	m := map[string]int{"a": 1}
	var x any = 2
	ch := make(chan int, 1)
	ch <- 3
	v1, ok1 := (m["a"])
	v2, ok2 := (x.(int))
	v3, ok3 := (<-ch)
	_, miss := (m["z"])
	n := v1 + v2*10 + v3*100
	if ok1 && ok2 && ok3 && !miss {
		n += 1000
	}
	return n // 1321
}

func parenCommaOkRhsAssignVar() int {
	m := map[string]int{"a": 4}
	var x any = "ab"
	ch := make(chan int, 1)
	ch <- 6
	var v1, v3 int
	var s string
	var ok1, ok2, ok3 bool
	v1, ok1 = (m["a"])
	s, ok2 = (x.(string))
	v3, ok3 = (<-ch)
	var v4, ok4 = (m["a"])
	var _, ok5 = (x.(int))
	n := v1 + len(s)*10 + v3*100 + v4*1000
	if ok1 && ok2 && ok3 && ok4 && !ok5 {
		n += 10000
	}
	return n // 14624
}

func main() {
	println("parenCommaOkRhsDefine", parenCommaOkRhsDefine())
	println("parenCommaOkRhsAssignVar", parenCommaOkRhsAssignVar())
}
