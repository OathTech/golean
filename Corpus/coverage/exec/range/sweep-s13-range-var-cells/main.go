package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: the RANGE forms'
// per-iteration variables (the decoder's desugar, not emitForPerIteration):
// a closure over the range-over-int variable, the address of the variable at
// each collection kind (int, slice index and value, map key and value, string
// index and rune, channel element, array value), and the body writing the
// variable without steering the iteration. range/range-loop-var-capture holds
// the slice-value capture; the function-iterator form refuses by name
// (FR-12). Expected = gc go1.26.5.

// D26
func intCapture() int {
	var fs []func() int
	for i := range 3 {
		fs = append(fs, func() int { return i })
	}
	return fs[0]()*100 + fs[1]()*10 + fs[2]() // 12
}

// D26b
func intAddr() int {
	var ps []*int
	for i := range 3 {
		ps = append(ps, &i)
	}
	return *ps[0]*100 + *ps[1]*10 + *ps[2] // 12
}

// D26c
func sliceValueAddr() int {
	var ps []*int
	for _, v := range []int{5, 6, 7} {
		ps = append(ps, &v)
	}
	return *ps[0]*100 + *ps[1]*10 + *ps[2] // 567
}

// D26d
func sliceIndexAddr() int {
	var ps []*int
	for i := range []int{5, 6, 7} {
		ps = append(ps, &i)
	}
	return *ps[0]*100 + *ps[1]*10 + *ps[2] // 12
}

// D26e (order-free sums)
func mapAddrs() int {
	m := map[int]int{1: 10, 2: 20}
	var ks []*int
	var vs []*int
	for k, v := range m {
		ks = append(ks, &k)
		vs = append(vs, &v)
	}
	return *ks[0] + *ks[1] + *vs[0] + *vs[1] // 33
}

// D26f
func stringAddrs() int {
	var is []*int
	var rs []*rune
	for i, r := range "ab" {
		is = append(is, &i)
		rs = append(rs, &r)
	}
	return (*is[0]*10+*is[1])*1000 + int(*rs[0]-'a')*10 + int(*rs[1]-'a') // 1001
}

// D26g
func chanAddr() int {
	ch := make(chan int, 3)
	ch <- 1
	ch <- 2
	ch <- 3
	close(ch)
	var ps []*int
	for v := range ch {
		ps = append(ps, &v)
	}
	return *ps[0]*100 + *ps[1]*10 + *ps[2] // 123
}

// D26i
func arrayValueAddr() int {
	a := [3]int{4, 5, 6}
	var ps []*int
	for _, v := range a {
		ps = append(ps, &v)
	}
	return *ps[0]*100 + *ps[1]*10 + *ps[2] // 456
}

// D34: the body writes the range-over-int variable.
func intBodyWrite() int {
	count := 0
	last := 0
	for i := range 5 {
		i += 10
		count++
		last = i
	}
	return count*100 + last // 514
}

// D35: the body writes the slice index variable.
func sliceBodyWrite() int {
	count := 0
	sum := 0
	for i, v := range []int{1, 2, 3} {
		i += 10
		sum += i + v
		count++
	}
	return count*1000 + sum // 3039
}

func main() {
	println(intCapture(), intAddr(), sliceValueAddr(), sliceIndexAddr(), mapAddrs(), stringAddrs(), chanAddr(),
		arrayValueAddr(), intBodyWrite(), sliceBodyWrite())
}
