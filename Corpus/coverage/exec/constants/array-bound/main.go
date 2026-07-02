package main

func constantArrayBound() int {
	const n = 3
	var xs [n]int
	xs[0] = 4
	xs[2] = 5
	return len(xs)*100 + xs[0]*10 + xs[2]
}

func main() {
	constantArrayBound()
}
