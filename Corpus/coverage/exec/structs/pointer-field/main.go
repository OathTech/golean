package main

type pointerFieldStruct struct {
	n int
}

func structPointerField() int {
	p := &pointerFieldStruct{n: 2}
	p.n = 5
	return p.n
}

func main() {
	structPointerField()
}
