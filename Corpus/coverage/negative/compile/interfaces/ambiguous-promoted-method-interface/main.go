package main

type ambiguousInterfaceA struct{}

func (ambiguousInterfaceA) m() int {
	return 1
}

type ambiguousInterfaceB struct{}

func (ambiguousInterfaceB) m() int {
	return 2
}

type ambiguousInterfaceBoth struct {
	ambiguousInterfaceA
	ambiguousInterfaceB
}

type ambiguousInterfaceMethod interface {
	m() int
}

var _ ambiguousInterfaceMethod = ambiguousInterfaceBoth{}
