package main

// W1: v := mut() + a, a captured by mut. Reference set {1, 2}.
func w1() int {
	a := 1
	mut := func() int { a = 2; return 0 }
	v := mut() + a
	return v
}

func main() { println(w1()) }
