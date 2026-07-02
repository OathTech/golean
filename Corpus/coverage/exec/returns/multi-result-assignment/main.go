package main

func pair() (int, int) {
	return 2, 7
}

func multiResultAssignment() int {
	a, b := pair()
	return a*10 + b
}
