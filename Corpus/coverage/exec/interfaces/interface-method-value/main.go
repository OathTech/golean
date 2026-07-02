package main

type interfaceAdder interface {
	Add(int) int
}

type interfaceCounter struct {
	n int
}

func (c interfaceCounter) Add(x int) int {
	return c.n + x
}

func interfaceMethodValue() int {
	var x interfaceAdder = interfaceCounter{n: 5}
	f := x.Add
	return f(3)
}

func main() {
	interfaceMethodValue()
}
