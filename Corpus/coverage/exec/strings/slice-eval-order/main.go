package main

func stringSliceEvalOrder() int {
	log := 0
	source := func() string {
		log = log*10 + 1
		return "abcd"
	}
	lo := func() int {
		log = log*10 + 2
		return 1
	}
	hi := func() int {
		log = log*10 + 3
		return 3
	}
	s := source()[lo():hi()]
	return log*100 + len(s)*10 + int(s[0])
}
