package main

func closureTwoVarsOneClosure() int {
	a := 1
	b := 2
	swapish := func() { a, b = b, a+b }
	swapish()
	swapish()
	return a*100 + b
}

func main() {
	closureTwoVarsOneClosure()
}
