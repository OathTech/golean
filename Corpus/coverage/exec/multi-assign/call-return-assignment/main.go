package main

func multiAssignPair() (int, int) {
	return 3, 5
}

func callReturnAssignment() int {
	a, b := 1, 2
	a, b = multiAssignPair()
	return a*10 + b
}

func main() {
	callReturnAssignment()
}
