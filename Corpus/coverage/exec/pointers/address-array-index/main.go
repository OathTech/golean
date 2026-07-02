package main

func pointerAddressArrayIndex() int {
	a := [3]int{1, 2, 3}
	p := &a[1]
	*p = 9
	return a[0]*100 + a[1]*10 + a[2]
}

func main() {
	pointerAddressArrayIndex()
}
