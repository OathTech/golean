package main

type box struct {
	a int
	b int
}

func (x box) pair() (int, int) {
	return x.a, x.b
}

func fwd(x box) (int, int) {
	return x.pair()
}

func multiResultMethodForward() int {
	p, q := fwd(box{a: 2, b: 3})
	return p*10 + q
}

func main() {
	multiResultMethodForward()
}
