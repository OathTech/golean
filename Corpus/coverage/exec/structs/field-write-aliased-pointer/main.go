package main

type shared struct {
	n int
}

func fieldWriteAliasedPointer() int {
	s := shared{n: 1}
	p := &s
	q := &s
	p.n = 4
	q.n = q.n + 3
	return s.n
}

func main() {
	fieldWriteAliasedPointer()
}
