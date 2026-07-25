package main

func tripleV() (int, int, int) {
	return 7, 8, 9
}

func headAndRest(head int, xs ...int) int {
	total := head * 1000
	for i := 0; i < len(xs); i++ {
		total = total + xs[i]*(10-i)
	}
	return total + len(xs)
}

func multiResultIntoFixedVariadic() int {
	return headAndRest(tripleV())
}

func main() {
	multiResultIntoFixedVariadic()
}
