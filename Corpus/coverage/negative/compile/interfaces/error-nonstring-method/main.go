package main

type nonStringErrorMethod struct{}

func (nonStringErrorMethod) Error() int {
	return 1
}

var _ error = nonStringErrorMethod{}
