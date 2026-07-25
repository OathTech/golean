package main

func pairE() (int, int) {
	return 7, 8
}

func multiResultToExisting() int {
	a := 1
	b := 2
	a, b = pairE()
	return a*10 + b
}

func main() {
	multiResultToExisting()
}
