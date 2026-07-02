package main

func multiAssignRhsBeforeWrites() int {
	x := 1
	y := 0
	x, y = 2, x
	return x*10 + y
}

func main() {
	multiAssignRhsBeforeWrites()
}
