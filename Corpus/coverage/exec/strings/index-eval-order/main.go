package main

func stringIndexEvalOrder() int {
	log := 0
	source := func() string {
		log = log*10 + 1
		return "abc"
	}
	index := func() int {
		log = log*10 + 2
		return 1
	}
	b := source()[index()]
	return log*100 + int(b)
}
