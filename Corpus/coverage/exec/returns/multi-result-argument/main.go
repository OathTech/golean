package main

func pair() (int, int) {
	return 3, 4
}

func combine(a int, b int) int {
	return a*10 + b
}

func multiResultArgument() int {
	return combine(pair())
}
