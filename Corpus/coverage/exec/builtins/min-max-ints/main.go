package main

func builtinMinMaxInts() int {
	return min(3, 1, 2)*10 + max(3, 1, 2)
}

func main() {
	builtinMinMaxInts()
}
