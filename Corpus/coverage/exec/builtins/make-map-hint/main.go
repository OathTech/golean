package main

func builtinMakeMapHint() int {
	m := make(map[int]int, 8)
	m[3] = 4
	return len(m)*100 + m[3]
}

func main() {
	builtinMakeMapHint()
}
