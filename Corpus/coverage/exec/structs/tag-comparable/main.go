package main

type tagComparableStruct struct {
	X int `tag:"x"`
}

func structTagComparable() int {
	a := tagComparableStruct{X: 1}
	b := tagComparableStruct{X: 1}
	if a == b {
		return 1
	}
	return 0
}
