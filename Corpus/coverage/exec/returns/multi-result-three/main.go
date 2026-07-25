package main

func triple() (int, int, int) {
	return 1, 2, 3
}

func multiResultThree() int {
	a, b, c := triple()
	return a*100 + b*10 + c
}

func main() {
	multiResultThree()
}
