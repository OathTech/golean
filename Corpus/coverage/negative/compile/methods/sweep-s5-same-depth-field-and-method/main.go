package main

type fieldX struct{ x int }

type methodX struct{}

func (methodX) x() int { return 1 }

type both struct {
	fieldX
	methodX
}

func main() {
	var b both
	_ = b.x // a field and a method of one name at the same depth
}
