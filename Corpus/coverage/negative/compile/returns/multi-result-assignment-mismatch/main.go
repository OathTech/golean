package main

func pair() (int, int) {
	return 1, 2
}

func bad() {
	a, b, c := pair()
	_, _, _ = a, b, c
}
