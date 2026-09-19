package main

// W2: v := a[b[0]] + mut(), a and b captured. Reference set {10, 30, 40}.
func w2() int {
	a := make([]int, 2)
	b := make([]int, 1)
	a[0] = 10
	a[1] = 20
	b[0] = 0
	mut := func() int { a[0] = 30; a[1] = 40; b[0] = 1; return 0 }
	v := a[b[0]] + mut()
	return v
}

func main() { println(w2()) }
