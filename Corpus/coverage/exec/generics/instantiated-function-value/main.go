package main

type genericAddable interface {
	~int | ~int8
}

func genericAdd[T genericAddable](a T, b T) T {
	return a + b
}

func genericInstantiatedFunctionValue() int {
	f := genericAdd[int]
	g := genericAdd[int8]
	return f(2, 3)*10 + int(g(4, 5))
}

func main() {
	genericInstantiatedFunctionValue()
}
