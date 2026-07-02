package main

func functionReassign() int {
	f := func(x int) int {
		return x + 1
	}
	first := f(4)
	f = func(x int) int {
		return x * 3
	}
	return first*10 + f(4)
}

func main() {
	functionReassign()
}
