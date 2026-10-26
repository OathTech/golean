package main

// Blank and unexported fields in ONE package: identical types, convertible.
type A struct {
	_ int
	x int
	Y int
}
type B struct {
	_ int
	x int
	Y int
}

func probe() int {
	a := A{x: 1, Y: 2}
	pb := (*B)(&a)
	r := 0
	if *pb == (B{x: 1, Y: 2}) {
		r += 10
	}
	*pb = B{x: 3, Y: 4}
	r += a.x*100 + a.Y
	return r
}

func main() { println(probe()) }
