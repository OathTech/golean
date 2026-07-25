package main

func makeCounter() func() int {
	n := 0
	return func() int {
		n = n + 1
		return n
	}
}

func closureReturnsClosure() int {
	c1 := makeCounter()
	c2 := makeCounter()
	a := c1()
	b := c1()
	c := c2()
	return a*100 + b*10 + c
}

func main() {
	closureReturnsClosure()
}
