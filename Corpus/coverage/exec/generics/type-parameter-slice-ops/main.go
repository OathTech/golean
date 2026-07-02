package main

type genericInts []int

func bumpMiddle[S ~[]int](s S) int {
	s[1] += len(s)
	return s[0]*100 + s[1]*10 + s[2]
}

func genericTypeParameterSliceOps() int {
	xs := genericInts{1, 2, 3}
	return bumpMiddle(xs)
}
