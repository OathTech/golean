package main

func mapLiteralEvalOrder() int {
	state := 0
	key := func(mark int) int {
		state = state*10 + mark
		return 1
	}
	value := func(mark int) int {
		state = state*10 + mark
		return mark
	}
	m := map[int]int{
		key(1): value(2),
		key(3): value(4),
	}
	return state*100 + len(m)*10 + m[1]
}

func main() {
	mapLiteralEvalOrder()
}
