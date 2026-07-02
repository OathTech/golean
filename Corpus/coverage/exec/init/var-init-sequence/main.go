package main

var varInitSequenceTrace int

func varInitSequenceStep(x int) int {
	varInitSequenceTrace = varInitSequenceTrace*10 + x
	return x
}

var varInitSequenceA = varInitSequenceStep(1)
var varInitSequenceB = varInitSequenceStep(2)

func varInitSequence() int {
	return varInitSequenceTrace*100 + varInitSequenceA*10 + varInitSequenceB
}

func main() {
	varInitSequence()
}
