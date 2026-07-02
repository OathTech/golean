package main

func pointerSliceHeader() int {
	s := []int{1, 2}
	p := &s
	*p = append(*p, 3)
	(*p)[0] = 9
	return len(s)*100 + s[0]*10 + s[2]
}

func main() {
	pointerSliceHeader()
}
