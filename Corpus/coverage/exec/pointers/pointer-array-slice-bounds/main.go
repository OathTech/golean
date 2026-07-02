package main

func pointerArraySliceBoundsPanic() int {
	a := [2]int{1, 2}
	p := &a
	hi := 3
	s := p[:hi]
	return len(s)
}
