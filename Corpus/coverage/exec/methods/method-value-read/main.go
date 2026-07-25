package main

type readBox struct {
	n int
}

func (b readBox) get(dst *int) {
	*dst = b.n
}

func methodValueRead() int {
	b := readBox{n: 7}
	f := b.get
	r := 0
	f(&r)
	g := readBox{n: 3}.get
	s := 0
	g(&s)
	return r*10 + s
}

func main() {
	methodValueRead()
}
