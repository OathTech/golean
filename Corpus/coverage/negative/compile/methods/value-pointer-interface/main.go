package main

type pointerOnlyInterface interface {
	m()
}

type pointerOnlyValue struct{}

func (*pointerOnlyValue) m() {}

var _ pointerOnlyInterface = pointerOnlyValue{}
