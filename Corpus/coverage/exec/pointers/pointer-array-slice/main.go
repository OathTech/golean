package main

func pointerArraySlice() int {
	a := [4]int{1, 2, 3, 4}
	p := &a
	s := p[1:3]
	s[0] = 9
	return a[1]*100 + len(s)*10 + cap(s)
}
