package main

type inner struct {
	n int
}

type outer struct {
	in  inner
	tag int
}

func nestedFieldWrite() int {
	o := outer{in: inner{n: 1}, tag: 2}
	o.in.n = 7
	o.tag = 3
	return o.in.n*10 + o.tag
}

func main() {
	nestedFieldWrite()
}
