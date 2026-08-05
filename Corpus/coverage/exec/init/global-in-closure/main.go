package main

var closureBase = 7
var closureLog int

var closureStep = func(x int) int {
	closureLog = closureLog*10 + x
	return closureBase + x
}

func globalInClosure() int {
	a := closureStep(1)
	closureBase = 20
	b := closureStep(2)
	return (closureLog*100+a)*100 + b
}

func main() {
	globalInClosure()
}
