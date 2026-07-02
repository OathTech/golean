package main

func multiAssignLhsIndexEvalOrder() int {
	s := []int{0, 0}
	i := 0
	next := func() int {
		old := i
		i++
		return old
	}
	s[next()], s[next()] = 4, 5
	return i*100 + s[0]*10 + s[1]
}

func main() {
	multiAssignLhsIndexEvalOrder()
}
