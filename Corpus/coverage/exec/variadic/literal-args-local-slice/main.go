package main

func variadicSetFirst(xs ...int) int {
	xs[0] = 7
	return xs[0]*10 + len(xs)
}

func variadicLiteralArgsLocalSlice() int {
	return variadicSetFirst(1, 2, 3)
}

func main() {
	variadicLiteralArgsLocalSlice()
}
