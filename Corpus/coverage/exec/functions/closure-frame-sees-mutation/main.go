package main

func closureFrameSeesMutation() int {
	x := 1
	set := func(v int) { x = v }
	before := x
	set(9)
	after := x
	return before*100 + after*10 + x
}

func main() {
	closureFrameSeesMutation()
}
