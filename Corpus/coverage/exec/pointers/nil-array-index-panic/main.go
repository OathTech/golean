package main

func pointerNilArrayIndexPanic() int {
	var p *[2]int
	return p[0]
}
