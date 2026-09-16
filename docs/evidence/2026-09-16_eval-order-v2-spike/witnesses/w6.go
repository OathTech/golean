package main

// F6 witness: one read against two ordered mutations. Relation set {0, 1, 2}.
func main() {
	x := 0
	inc := func() int { x++; return 0 }
	v := x + inc() + inc()
	println("w6", v)
}
