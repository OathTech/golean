package main

type reader = interface {
	Val() int
}

type cell int

func (c cell) Val() int {
	return int(c) * 3
}

func anonymousAliasDispatch() int {
	var r reader = cell(4)
	return r.Val()
}

func main() {
	anonymousAliasDispatch()
}
