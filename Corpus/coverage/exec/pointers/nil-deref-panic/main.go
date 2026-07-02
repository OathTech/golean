package main

func pointerNilDerefPanic() int {
	var p *int
	return *p
}

func main() {
	pointerNilDerefPanic()
}
