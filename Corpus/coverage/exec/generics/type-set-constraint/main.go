package main

type smallInt interface {
	~int | ~int8
}

type myInt int

func addSmall[T smallInt](a T, b T) int {
	return int(a + b)
}

func genericTypeSetConstraint() int {
	return addSmall(myInt(2), myInt(3))*10 + addSmall(int8(4), int8(5))
}

func main() {
	genericTypeSetConstraint()
}
