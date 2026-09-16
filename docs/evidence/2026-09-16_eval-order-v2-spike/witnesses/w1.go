package main

// F1 witness: a mutable read RIGHT of a mutating call. Relation set {1, 2}.
func main() {
	a := 1
	mut := func() int { a = 2; return 0 }
	v := mut() + a
	println("w1", v)
}
