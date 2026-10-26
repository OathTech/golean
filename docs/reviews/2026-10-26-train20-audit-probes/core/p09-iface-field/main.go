package main

// A struct with an interface-typed field: equality through the alias compares
// the dynamic values; the whole store through the alias replaces the box.
type A struct {
	I any
	N int
}
type B struct {
	I any
	N int
}

func probe() int {
	a := A{3, 1}
	pb := (*B)(&a)
	r := 0
	if *pb == (B{3, 1}) {
		r += 10
	}
	*pb = B{"s", 2}
	if s, ok := a.I.(string); ok && s == "s" {
		r += 1
	}
	return r + a.N*100
}

func main() { println(probe()) }
