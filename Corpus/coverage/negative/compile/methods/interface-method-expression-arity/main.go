package main

type methodExpressionInterface interface {
	M() int
}

func main() {
	f := methodExpressionInterface.M
	_ = f()
}
