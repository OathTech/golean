package main

func arrayNestedCopyValue() int {
	a := [2][2]int{{1, 2}, {3, 4}}
	b := a
	b[0][1] = 9
	return a[0][1]*10 + b[0][1]
}

func main() {
	arrayNestedCopyValue()
}
