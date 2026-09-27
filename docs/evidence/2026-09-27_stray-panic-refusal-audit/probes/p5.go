package main

type S struct {
	x  int
	ys [2]int
}

func build() (s S, arr [3]int) {
	s.x = 1
	p := &s.ys[1]
	*p = 2
	q := &arr[2]
	defer func() { *q = 9; arr[0] = s.ys[1] }()
	return
}

func probe() int {
	s, arr := build()
	println(s.x, s.ys[0], s.ys[1], arr[0], arr[1], arr[2])
	return s.x + s.ys[1]*10 + arr[0]*100 + arr[2]*1000
}

func main() { println(probe()) }
