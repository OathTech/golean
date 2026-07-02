package main

func pointerDerefAssign() int {
	x := 4
	p := &x
	*p = *p + 7
	return x
}

func main() {
	pointerDerefAssign()
}
