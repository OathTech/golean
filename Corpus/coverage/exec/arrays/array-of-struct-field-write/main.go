package main

type cell struct {
	v int
}

func arrayOfStructFieldWrite() int {
	var xs [3]cell
	xs[1].v = 5
	xs[2].v = xs[1].v + 2
	return xs[0].v*100 + xs[1].v*10 + xs[2].v
}

func main() {
	arrayOfStructFieldWrite()
}
