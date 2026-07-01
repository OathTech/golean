package main

func interfaceComparePanic() int {
	var a any = []int{1}
	var b any = []int{1}
	if a == b {
		return 1
	}
	return 0
}
