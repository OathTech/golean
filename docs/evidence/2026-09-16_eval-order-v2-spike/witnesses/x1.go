package main

// Fragment extra: assignment phases (E4 shape) — a failing target operand
// and a failing RHS operand, both phase 1. Two panic identities.
func main() {
	defer func() { println("x1 panic:", recover().(error).Error()) }()
	xs, ys, zs := make([]int, 3), make([]int, 3), make([]int, 3)
	var b int
	xs[ys[9]], b = zs[7], 2
	println("x1 ok", b)
}
