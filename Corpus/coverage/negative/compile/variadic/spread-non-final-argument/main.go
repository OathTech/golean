package main

func sum(xs ...int) int {
	return len(xs)
}

func bad() int {
	xs := []int{1, 2}
	return sum(xs..., 3)
}
