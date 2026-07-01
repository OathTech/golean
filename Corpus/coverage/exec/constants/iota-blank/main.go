package main

const (
	zero = iota
	_
	two
	_
	four
)

func iotaBlank() int {
	return zero*100 + two*10 + four
}
