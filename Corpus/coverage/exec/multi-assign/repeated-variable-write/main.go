package main

func repeatedVariableWrite() int {
	x := 0
	x, x = 1, 2
	return x
}

func main() {
	repeatedVariableWrite()
}
