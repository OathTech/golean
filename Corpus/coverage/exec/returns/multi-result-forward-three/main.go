package main

func tripleSrc() (int, int, int) {
	return 4, 5, 6
}

func forwardTriple() (int, int, int) {
	return tripleSrc()
}

func multiResultForwardThree() int {
	a, b, c := forwardTriple()
	return a*100 + b*10 + c
}

func main() {
	multiResultForwardThree()
}
