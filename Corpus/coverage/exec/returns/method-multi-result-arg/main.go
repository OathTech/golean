package main

type pairSrc struct{ a, b int }

func (p pairSrc) pair() (int, int) {
	return p.a, p.b
}

func take(x int, y int) int {
	return x*10 + y
}

func methodMultiResultArg() int {
	p := pairSrc{a: 4, b: 5}
	return take(p.pair())
}

func main() {
	methodMultiResultArg()
}
