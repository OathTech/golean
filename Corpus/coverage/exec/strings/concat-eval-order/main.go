package main

func stringConcatEvalOrder() int {
	log := 0
	left := func() string {
		log = log*10 + 1
		return "a"
	}
	right := func() string {
		log = log*10 + 2
		return "b"
	}
	s := left() + right()
	return len(s)*100 + log
}
