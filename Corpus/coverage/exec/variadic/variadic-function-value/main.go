package main

func variadicFunctionValueSum(xs ...int) int {
	total := 0
	for _, x := range xs {
		total += x
	}
	return total
}

func variadicFunctionValue() int {
	f := variadicFunctionValueSum
	xs := []int{1, 2, 3, 4}
	return f(xs...)
}
