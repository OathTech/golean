package main

type variadicDefinedInt int

func variadicGenericSum[T ~int](xs ...T) int {
	total := 0
	for _, x := range xs {
		total += int(x)
	}
	return total
}

func variadicGeneric() int {
	xs := []variadicDefinedInt{1, 3, 4}
	return variadicGenericSum(xs...)
}
