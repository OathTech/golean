package main

var bareCallTrace int

func bareCallStep() int {
	bareCallTrace = bareCallTrace*10 + 4
	return 9
}

func bareCallDiscardResult() int {
	bareCallStep()
	return bareCallTrace
}

func main() {
	bareCallDiscardResult()
}
