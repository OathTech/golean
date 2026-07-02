package main

func variadicMutateFirst(xs ...int) int {
	xs[0] = 9
	return len(xs)
}

func variadicSpreadAliasing() int {
	s := []int{1, 2}
	n := variadicMutateFirst(s...)
	return s[0]*10 + n
}

func main() {
	variadicSpreadAliasing()
}
