package main

type duplicateEmbeddedA interface {
	m() int
}

type duplicateEmbeddedB interface {
	m() int
}

type duplicateEmbeddedBoth interface {
	duplicateEmbeddedA
	duplicateEmbeddedB
}

type duplicateEmbeddedValue struct {
	n int
}

func (v duplicateEmbeddedValue) m() int {
	return v.n
}

func embeddedInterfaceDuplicateMethod() int {
	var x duplicateEmbeddedBoth = duplicateEmbeddedValue{n: 11}
	return x.m()
}
