package main

func variadicPair() (int, int) {
	return 4, 5
}

func collectVariadic(xs ...int) int {
	return len(xs)*100 + xs[0]*10 + xs[1]
}

func variadicMultiResultCall() int {
	return collectVariadic(variadicPair())
}
