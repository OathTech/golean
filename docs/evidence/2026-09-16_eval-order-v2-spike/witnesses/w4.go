package main

// F4 witness: two independent failing operands, no event. Both identities.
func main() {
	defer func() { println("w4 panic:", recover().(error).Error()) }()
	var a, b []int
	_ = a[1] + b[2]
	println("w4 ok")
}
