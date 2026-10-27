package main

// S6 sweep, group O: the stores are carried out LEFT TO RIGHT — an aliasing
// pair of targets keeps the RIGHT one's value (spec: `x[0], x[0] = 1, 2`
// leaves 2), on every target kind and value source.

type oT struct{ x int }

// O.3: two deref targets through one pointer.
func oDerefAlias() int {
	v := 0
	p := &v
	q := p
	*p, *q = 1, 2
	return v
}

// O.4: the same map key twice.
func oMapSameKey() int {
	m := map[int]int{}
	m[1], m[1] = 1, 2
	return m[1]*10 + len(m)
}

// O.5: two slice headers over one array.
func oSliceAlias() int {
	arr := [2]int{}
	s := arr[:]
	t := arr[:1]
	s[0], t[0] = 1, 2
	return arr[0]
}

// O.6: the same field through two pointers.
func oFieldAlias() int {
	p := &oT{}
	q := p
	p.x, q.x = 1, 2
	return p.x
}

// O.7: a comma-ok map read into ONE variable — the ok store lands last.
func oCommaOkMapSameVar() int {
	m := map[int]bool{1: false}
	b := false
	b, b = m[1]
	if b {
		return 1
	}
	return 0
}

// O.8: a comma-ok type assertion into one variable.
func oCommaOkAssertSameVar() int {
	var iv any = false
	b := false
	b, b = iv.(bool)
	if b {
		return 1
	}
	return 0
}

// O.9: a comma-ok receive into one variable.
func oRecvSameVar() int {
	ch := make(chan bool, 1)
	ch <- false
	b := false
	b, b = <-ch
	if b {
		return 1
	}
	return 0
}

// O.10: the select clause form.
func oSelectRecvSameVar() int {
	ch := make(chan bool, 1)
	ch <- false
	b := false
	select {
	case b, b = <-ch:
	}
	if b {
		return 1
	}
	return 0
}

// O.11: the range clause's per-iteration assignment, key and value into one
// variable — the value lands last.
func oRangeSameVar() int {
	i := 0
	sum := 0
	for i, i = range []int{5, 6, 7} {
		sum += i
	}
	return sum*10 + i
}

// O.14: in a generic function.
func oSet2[T any](p, q *T, a, b T) {
	*p, *q = a, b
}

func oGenericDerefAlias() int {
	v := 0
	oSet2(&v, &v, 1, 2)
	return v
}

// O.15: three targets, the first repeated.
func oThreeTargetsRepeat() int {
	x, y := 0, 0
	x, y, x = 1, 2, 3
	return x*10 + y
}

// O.16: a multi-value call into two deref targets through one pointer.
func oPair() (int, int) { return 1, 2 }
func oCallDerefAlias() int {
	v := 0
	p := &v
	*p, *p = oPair()
	return v
}

func main() {
	oDerefAlias()
}
