package main

type leafBox struct {
	n int
}

type hopBox struct {
	leaf *leafBox
}

func pointerHopFieldWrite() int {
	l := leafBox{n: 1}
	h := hopBox{leaf: &l}
	h.leaf.n = 9
	return l.n
}

func main() {
	pointerHopFieldWrite()
}
