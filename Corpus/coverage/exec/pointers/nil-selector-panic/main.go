package main

type pointerSelectorRecord struct {
	x int
}

func pointerNilSelectorPanic() int {
	var p *pointerSelectorRecord
	return p.x
}
