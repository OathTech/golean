package main

// Round-4 pin (BUG-035): a blank among the targets must not change the
// phase structure — `i, _, a[i] = …` still captures a[i]'s index
// operand in phase 1 (the spec's own `i, a[i]` rule). The
// temps-plus-single-assigns blank lowering stores i first and then
// reads the POST-store i for the index.

func blankDepIndex() int {
	i := 0
	a := []int{10, 20, 30}
	i, _, a[i] = 2, 0, 99
	return i*10000 + a[0]*100 + a[1]
}

func main() {
	println(blankDepIndex())
}
