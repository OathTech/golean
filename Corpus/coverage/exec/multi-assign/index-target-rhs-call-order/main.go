package main

func indexTargetRhsCallOrder() int {
	xs := []int{10, 20, 30}
	i := 0
	bump := func() int {
		i = 2
		return 7
	}
	xs[i] = bump()
	return xs[0]*100 + xs[1]*10 + xs[2] + i
}

func main() {
	indexTargetRhsCallOrder()
}
