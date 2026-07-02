package main

func pickSecond[T any](first T, second T) T {
	_ = first
	return second
}

func genericInference() int {
	return pickSecond(2, 5) + len(pickSecond("x", "abc"))
}

func main() {
	genericInference()
}
