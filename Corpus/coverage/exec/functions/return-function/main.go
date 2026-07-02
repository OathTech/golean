package main

func makeReturnFunctionAdder(base int) func(int) int {
	return func(x int) int {
		return base + x
	}
}

func returnFunction() int {
	add7 := makeReturnFunctionAdder(7)
	add2 := makeReturnFunctionAdder(2)
	return add7(5)*10 + add2(3)
}

func main() {
	returnFunction()
}
