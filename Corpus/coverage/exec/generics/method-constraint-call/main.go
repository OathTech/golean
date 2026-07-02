package main

type genericDoubler interface {
	Double() int
}

type genericNumber int

func (n genericNumber) Double() int {
	return int(n) * 2
}

func callDouble[T genericDoubler](x T) int {
	return x.Double()
}

func genericMethodConstraintCall() int {
	return callDouble(genericNumber(6))
}

func main() {
	genericMethodConstraintCall()
}
