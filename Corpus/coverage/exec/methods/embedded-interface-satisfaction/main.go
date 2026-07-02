package main

type embeddedInterfaceBase struct {
	n int
}

func (b embeddedInterfaceBase) m() int {
	return b.n + 3
}

type embeddedInterfaceOuter struct {
	embeddedInterfaceBase
}

type embeddedMethodInterface interface {
	m() int
}

func embeddedInterfaceSatisfaction() int {
	var x embeddedMethodInterface = embeddedInterfaceOuter{embeddedInterfaceBase: embeddedInterfaceBase{n: 4}}
	return x.m()
}
