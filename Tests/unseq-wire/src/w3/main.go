package main

// W3: a[i] += mut() with mut setting i = 1 and returning 1; a private (its
// elements are heap). Reference set {"w3 11 20", "w3 10 21"}; "w3 10 11" forbidden.
func w3() {
	a := make([]int, 2)
	a[0] = 10
	a[1] = 20
	i := 0
	mut := func() int { i = 1; return 1 }
	a[i] += mut()
	println("w3", a[0], a[1])
}

func main() { w3() }
