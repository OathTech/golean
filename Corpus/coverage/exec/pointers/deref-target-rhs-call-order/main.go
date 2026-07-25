package main

func derefTargetRhsCallOrder() int {
	x := 1
	y := 2
	p := &x
	swapP := func() int {
		p = &y
		return 9
	}
	*p = swapP()
	return x*10 + y
}

func main() {
	derefTargetRhsCallOrder()
}
