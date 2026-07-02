package main

func newDistinctAllocations() int {
	p := new(int)
	q := new(int)
	*p = 3
	*q = 4
	if p == q {
		return 0
	}
	return *p*10 + *q
}

func main() {
	newDistinctAllocations()
}
