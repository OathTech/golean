package main

type poisonBox[T any] struct {
	c chan T
}

func poisonHelper() int {
	var b poisonBox[int]
	b.c <- 1
	return 0
}

func genericQuarantinedInstantiation() int {
	return 21
}

func main() {
	genericQuarantinedInstantiation()
}
