package main

func arrayKeyedLiteralSparse() int {
	a := [5]int{2: 7, 4: 9}
	return len(a)*1000 + a[0]*100 + a[2]*10 + a[4]
}

func main() {
	arrayKeyedLiteralSparse()
}
