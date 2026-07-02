package main

type copiedStruct struct {
	n int
}

func structCopyValue() int {
	a := copiedStruct{n: 1}
	b := a
	b.n = 7
	return a.n*10 + b.n
}

func main() {
	structCopyValue()
}
