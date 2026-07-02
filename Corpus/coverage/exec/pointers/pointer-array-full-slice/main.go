package main

func pointerArrayFullSlice() int {
	a := [4]int{1, 2, 3, 4}
	p := &a
	s := p[1:3:3]
	s = append(s, 99)
	return a[1]*100 + a[3]*10 + s[2]
}
