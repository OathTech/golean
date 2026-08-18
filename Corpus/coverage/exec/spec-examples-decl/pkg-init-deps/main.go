package main

// spec#Package_initialization block Package_initialization-2-5310cffb:
// dependency-ordered initialization — the order is d, b, c, a; f increments
// d each call, so b == 4, c == 5, a == c + b == 9, and d == 5 once
// initialization has finished. (The spec also notes a = c + b and a = b + c
// give the same order.)

var (
	a = c + b // == 9
	b = f()   // == 4
	c = f()   // == 5
	d = 3     // == 5 after initialization has finished
)

func f() int {
	d++
	return d
}

func pkgInitDeps() int {
	return a*1000 + b*100 + c*10 + d // 9455
}
