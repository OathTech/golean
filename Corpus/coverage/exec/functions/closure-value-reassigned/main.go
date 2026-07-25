package main

func closureValueReassigned() int {
	x := 0
	f := func() { x = x*10 + 1 }
	f()
	f = func() { x = x*10 + 2 }
	f()
	return x
}

func main() {
	closureValueReassigned()
}
