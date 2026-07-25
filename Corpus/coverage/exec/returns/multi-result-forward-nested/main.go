package main

func pairN() (int, int) {
	return 3, 4
}

func combineN(a int, b int) int {
	return a*10 + b
}

func wrapCombine() int {
	return combineN(pairN())
}

func multiResultForwardNested() int {
	return wrapCombine() + 1
}

func main() {
	multiResultForwardNested()
}
