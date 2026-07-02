package main

func interfaceArrayComparePanic() int {
	a := [1]any{[]int{1}}
	b := [1]any{[]int{1}}
	if a == b {
		return 1
	}
	return 0
}
