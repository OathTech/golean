package main

func orderedPair() (int, int) {
	return 1, 2
}

func multiResultAssignOrder() int {
	a := []int{0, 0, 0}
	i := 0
	i, a[i] = orderedPair()
	return i*100 + a[0]*10 + a[1]
}
