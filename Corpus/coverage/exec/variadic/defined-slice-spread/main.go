package main

type variadicInts []int

func variadicLen(xs ...int) int {
	return len(xs)*10 + xs[1]
}

func variadicDefinedSliceSpread() int {
	xs := variadicInts{4, 5, 6}
	return variadicLen(xs...)
}

func main() {
	variadicDefinedSliceSpread()
}
