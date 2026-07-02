package main

func sliceExprEvalOrder() int {
	log := 0
	source := func() []int {
		log = log*10 + 1
		return []int{0, 1, 2, 3, 4}
	}
	lo := func() int {
		log = log*10 + 2
		return 1
	}
	hi := func() int {
		log = log*10 + 3
		return 4
	}
	xs := source()[lo():hi()]
	return log*100 + len(xs)*10 + xs[0]
}
