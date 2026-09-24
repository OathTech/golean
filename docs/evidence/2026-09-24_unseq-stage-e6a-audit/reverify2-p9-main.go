package main

// Re-verification 2 probes — range constructs the scoped binder rule might still leak or now over-refuse.

func wit(x int) int { println("wit", x); return x }

func rBodyRedeclaresKey() int { // the body redeclares the key with another type; a graph after the loop uses an outer int i
	i := 5
	s := []int{7, 8}
	r := 0
	for i := range s {
		i := "x" + string(rune('a'+i))
		r += len(i)
	}
	return s[i-5] + wit(1) + r
}

func rNestedReuse() int { // nested ranges reusing i with different element types; graphs in both bodies and after each loop
	i := "ab"
	ss := [][]int{{7}, {8}}
	r := 0
	for i, s := range ss {
		for i, v := range s {
			r += s[i] + v + wit(1)
		}
		r += ss[i][0] + wit(2)
	}
	return len(i) + r
}

func rLabelledContinue() int {
	k := "ab"
	s := []int{7, 8}
	r := 0
L:
	for _, k := range s {
		if k == 7 {
			continue L
		}
		r += k + wit(1)
	}
	return s[len(k)-2] + wit(2) + r
}

func rMapShadow() int { // outer k, v strings shadowed by the map range's int key/value; a graph after uses the outer ones
	k, v := "ab", "abc"
	m := map[int]int{0: 1}
	s := []int{7, 8}
	r := 0
	for k, v := range m {
		r += k + v
	}
	return s[len(k)-2] + s[len(v)-3] + wit(1) + r
}

func rStringShadow() int { // outer i, c strings shadowed by the string range's int / rune vars
	i, c := "ab", "abc"
	s := []int{7, 8}
	r := 0
	for i, c := range "z" {
		r += i + int(c) - 'z'
	}
	return s[len(i)-2] + s[len(c)-3] + wit(1) + r
}

func rChanShadow() int {
	v := "ab"
	ch := make(chan int, 1)
	ch <- 3
	close(ch)
	s := []int{7, 8}
	r := 0
	for v := range ch {
		r += v
	}
	return s[len(v)-2] + wit(1) + r
}

func rIntShadow() int {
	i := "ab"
	s := []int{7, 8}
	r := 0
	for i := range 2 {
		r += i
	}
	return s[len(i)-2] + wit(1) + r
}

func rSequential() int { // two sequential ranges reusing k with different types, graphs after each
	k := "ab"
	s := []int{7, 8}
	t := []string{"x"}
	r := s[len(k)-2] + wit(1)
	for _, k := range s {
		r += k
	}
	r += s[len(k)-2] + wit(2)
	for _, k := range t {
		r += len(k)
	}
	return s[len(k)-2] + wit(3) + r
}

func rInSelectClause() int { // a range inside a select clause body shadowing an outer k; a graph after the select uses the outer k
	k := "ab"
	ch := make(chan int, 1)
	ch <- 0
	s := []int{7, 8}
	r := 0
	select {
	case v := <-ch:
		for _, k := range s {
			r += k + v
		}
	}
	return s[len(k)-2] + wit(1) + r
}

func rInLabelledBlock() int {
	k := "ab"
	s := []int{7, 8}
	r := 0
	goto L
L:
	{
		for _, k := range s {
			r += k
		}
	}
	return s[len(k)-2] + wit(1) + r
}

func rInLiftedClosure() int { // the range lives in a lifted closure; the enclosing graph uses the outer k after the call
	k := "ab"
	s := []int{7, 8}
	f := func() int {
		r := 0
		for _, k := range s {
			r += k
		}
		return r
	}
	return f() + s[len(k)-2] + wit(1)
}

func rBodyGraphAndAfter() int { // a graph INSIDE the body uses the range k (int); a graph AFTER uses the outer k (string)
	k := "ab"
	s := []int{7, 8}
	r := 0
	for _, k := range s {
		r += s[k-7] + wit(1)
	}
	return s[len(k)-2] + wit(2) + r
}

func rSameTypeShadow() int { // same-type shadow: the leak never bit here; must still run
	k := 0
	s := []int{7, 8}
	r := 0
	for _, k := range s {
		r += k
	}
	return s[k] + wit(1) + r
}

func rKeyOnlyBlankValue() int {
	i := "ab"
	s := []int{7, 8}
	r := 0
	for i, _ := range s {
		r += i
	}
	return s[len(i)-2] + wit(1) + r
}

func main() {}
