package main

func closureArgAndCapture() int {
	base := 10
	f := func(x int, y int) int { return base*100 + x*10 + y }
	r1 := f(2, 3)
	base = 20
	r2 := f(4, 5)
	return r1 + r2
}

func main() {
	closureArgAndCapture()
}
