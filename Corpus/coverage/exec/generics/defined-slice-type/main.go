package main

type genericVec[T any] []T

func genericDefinedSliceType() int {
	xs := genericVec[int]{1, 2, 3}
	return len(xs)*100 + xs[1]*10 + xs[2]
}

func main() {
	genericDefinedSliceType()
}
