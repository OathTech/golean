package main

func pairB() (int, int) {
	return 5, 6
}

func multiResultBlankForward() int {
	_, b := pairB()
	return b * 3
}

func main() {
	multiResultBlankForward()
}
