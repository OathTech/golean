package main

func bad() []int {
	return [3]int{1, 2, 3}[:]
}
