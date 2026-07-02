package main

func pair() (int, int) {
	return 4, 5
}

func bad() []int {
	return append([]int{1, 2}, pair())
}
