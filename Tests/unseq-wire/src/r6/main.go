package main

// R6: v := a[f()] with f rebinding a — SPLIT header producer + checked access {10, 20};
// the FUSED read (the narrowing) {20}.
func r6() int {
	a := make([]int, 1)
	a[0] = 10
	b := make([]int, 1)
	b[0] = 20
	f := func() int { a = b; return 0 }
	v := a[f()]
	return v
}

func main() { println(r6()) }
