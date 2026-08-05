package main

type readyIface[T any] interface {
	Ready() <-chan T
}

func poisonIfaceHelper() int {
	var r readyIface[int]
	_ = r
	ch := make(chan int, 1)
	_ = ch
	return 0
}

func genericQuarantinedInterface() int {
	return 22
}

func main() {
	genericQuarantinedInterface()
}
