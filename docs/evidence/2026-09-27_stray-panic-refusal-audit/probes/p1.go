package main

func named() (a, b int) {
	p := &a
	defer func() {
		if r := recover(); r != nil {
			*p += 10
			b = a * 2
		}
	}()
	a = 1
	var xs []int
	_ = xs[3]
	return 5, 6
}

func namedNoPanic() (r int) {
	defer func() { r *= 3 }()
	q := &r
	*q = 4
	return r + 1
}

func probe() int {
	a, b := named()
	c := namedNoPanic()
	println(a, b, c)
	return a*10000 + b*100 + c
}

func main() { println(probe()) }
