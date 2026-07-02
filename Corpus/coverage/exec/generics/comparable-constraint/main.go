package main

func indexOf[T comparable](xs []T, target T) int {
	for i, x := range xs {
		if x == target {
			return i
		}
	}
	return -1
}

func genericComparableConstraint() int {
	return indexOf([]string{"a", "b", "c"}, "b")*10 + indexOf([]int{3, 4}, 5)
}

func main() {
	genericComparableConstraint()
}
