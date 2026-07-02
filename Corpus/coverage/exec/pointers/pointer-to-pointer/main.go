package main

func pointerToPointerAlias() int {
	x := 3
	p := &x
	pp := &p
	**pp = 8
	y := 5
	*pp = &y
	**pp = **pp + x
	return x*100 + y
}

func main() {
	pointerToPointerAlias()
}
