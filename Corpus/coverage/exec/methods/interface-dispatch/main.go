package main

type methodDispatchInterface interface {
	value() int
}

type methodDispatchBox struct {
	n int
}

func (b methodDispatchBox) value() int {
	return b.n + 1
}

func methodInterfaceDispatch() int {
	var x methodDispatchInterface = methodDispatchBox{n: 4}
	return x.value()
}

func main() {
	methodInterfaceDispatch()
}
