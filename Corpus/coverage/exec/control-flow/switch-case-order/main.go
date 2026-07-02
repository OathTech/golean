package main

func switchCaseOrder() int {
	seen := 0
	mark := func(v int) int {
		seen = seen*10 + v
		return v
	}
	switch 2 {
	case mark(1), mark(2):
		seen = seen*10 + 3
	case mark(4):
		seen = seen*10 + 5
	}
	return seen
}

func main() {
	switchCaseOrder()
}
