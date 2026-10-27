package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// The ASSIGN-form range (`for k, v = range x`, BUG-050's site) into
// interface-typed targets over the collection shapes BUG-050's rows do not
// hold: an array, a pointer to an array, a channel, an integer, a map's
// value, an array's index (the function-iterator form is quarantined by name and
// recorded as a coverage gap, not rowed).

func arrayValue() (any, int) {
	arr := [2]int{3, 4}
	var v any
	sum := 0
	for _, v = range arr {
		sum += v.(int)
	}
	return v, sum
}

func arrayIndex() (any, int) {
	arr := [3]string{"a", "b", "c"}
	var i any
	sum := 0
	for i = range arr {
		sum += i.(int)
	}
	return i, sum
}

func ptrArrayValue() (any, int) {
	arr := [2]int{5, 6}
	p := &arr
	var v any
	sum := 0
	for _, v = range p {
		sum += v.(int)
	}
	return v, sum
}

func chanElem() (any, int) {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	close(ch)
	var v any
	sum := 0
	for v = range ch {
		sum += v.(int)
	}
	return v, sum
}

func intRange() (any, int) {
	var i any
	sum := 0
	for i = range 3 {
		sum += i.(int)
	}
	return i, sum
}

func mapValue() (any, int) {
	m := map[string]int{"a": 1}
	var v any
	sum := 0
	for _, v = range m {
		sum += v.(int)
	}
	return v, sum
}


func main() {
	arrayValue()
}
