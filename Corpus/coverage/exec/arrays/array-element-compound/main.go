package main

func arrayElementCompound() int {
	trace := 0
	idx := func() int {
		trace++
		return 1
	}
	var xs [3]int
	xs[1] = 5
	xs[idx()] += 10
	xs[0]++
	return trace*1000 + xs[0]*100 + xs[1]
}

func main() {
	arrayElementCompound()
}
