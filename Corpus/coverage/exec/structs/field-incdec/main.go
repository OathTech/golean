package main

type tally struct {
	n int
}

func fieldIncDec() int {
	t := tally{n: 5}
	t.n++
	t.n++
	t.n--
	return t.n
}

func main() {
	fieldIncDec()
}
