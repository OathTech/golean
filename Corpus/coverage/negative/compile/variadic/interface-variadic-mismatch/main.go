package main

type variadicInterface interface {
	m(...int)
}

type variadicConcrete struct{}

func (variadicConcrete) m([]int) {
}

var _ variadicInterface = variadicConcrete{}
