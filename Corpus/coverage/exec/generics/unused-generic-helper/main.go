package main

func unusedHelper[T any](x T) T {
	return x
}

func genericUnusedHelperNeighbor() int {
	return 12
}

func main() {
	genericUnusedHelperNeighbor()
}
