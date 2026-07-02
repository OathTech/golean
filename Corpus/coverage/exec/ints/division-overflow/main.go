package main

func intDivisionOverflow() int {
	var x int8 = -128
	y := x / -1
	if y == -128 {
		return 1
	}
	return 0
}

func main() {
	intDivisionOverflow()
}
