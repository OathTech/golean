package main

type alpha struct{ n int }
type beta struct{ n int }

func (a alpha) mk() int {
	g := func() int { return 2 }
	return g()
}

func (b beta) mk() int {
	g := func() int { return 9 }
	return g()
}

func sameNameMethodClosures() int {
	var a alpha
	var b beta
	return a.mk()*10 + b.mk()
}

func main() {
	sameNameMethodClosures()
}
