package main

type holder struct {
	xs [3]int
}

func structArrayElementWrite() int {
	var h holder
	h.xs[0] = 1
	h.xs[2] = 3
	h.xs[1] = h.xs[0] + h.xs[2]
	return h.xs[0]*100 + h.xs[1]*10 + h.xs[2]
}

func main() {
	structArrayElementWrite()
}
