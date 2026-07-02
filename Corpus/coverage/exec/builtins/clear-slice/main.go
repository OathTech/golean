package main

func builtinClearSlice() int {
	s := []int{1, 2, 3}
	clear(s)
	return len(s)*100 + cap(s)*10 + s[0] + s[2]
}

func main() {
	builtinClearSlice()
}
