package main

// W6: v := x + inc() + inc(), x captured. Reference set {0, 1, 2}.
func w6() int {
	x := 0
	inc := func() int { x++; return 0 }
	v := x + inc() + inc()
	return v
}

func main() { println(w6()) }
