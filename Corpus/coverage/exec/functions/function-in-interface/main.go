package main

func applyFunctionFromInterface() int {
	var x any = func(n int) int {
		return n*2 + 1
	}
	f := x.(func(int) int)
	return f(20)
}
