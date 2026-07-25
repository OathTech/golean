package main

func closureParamShadowsCapture() int {
	x := 1
	f := func(x int) int { return x * 10 }
	r := f(7)
	return r*10 + x
}

func main() {
	closureParamShadowsCapture()
}
