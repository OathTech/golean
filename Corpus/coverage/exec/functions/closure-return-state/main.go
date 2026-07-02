package main

func makeCounterClosure(start int) func() int {
	x := start
	return func() int {
		x++
		return x
	}
}

func closureReturnState() int {
	next := makeCounterClosure(4)
	return next()*10 + next()
}

func main() {
	closureReturnState()
}
