package main

func closureNestedRecapture() int {
	x := 1
	outer := func() int {
		inner := func() int {
			x = x*10 + 2
			return x
		}
		x = x*10 + 3
		return inner()
	}
	r := outer()
	return r*10 + x
}

func main() {
	closureNestedRecapture()
}
