package main

func closureRecursion() int {
	var sum func(int) int
	sum = func(n int) int {
		if n == 0 {
			return 0
		}
		return n + sum(n-1)
	}
	return sum(4)
}
