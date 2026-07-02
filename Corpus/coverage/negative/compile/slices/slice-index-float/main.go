package main

func bad() []int {
	s := []int{1, 2, 3}
	return s[1.2:]
}
