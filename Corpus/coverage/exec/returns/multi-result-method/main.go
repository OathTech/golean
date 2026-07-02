package main

type source struct {
	a int
	b int
}

func (s source) pair() (int, int) {
	return s.a, s.b
}

func multiResultMethod() int {
	a, b := (source{a: 5, b: 6}).pair()
	return a*10 + b
}
