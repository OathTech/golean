package main

func divideByZero() {
	y := 0
	_ = 1 / y
}

func main() {
	divideByZero()
}
