package main

func ifInitBeforeCondition() int {
	state := 0
	next := func() int {
		state = 4
		return 7
	}
	if x := next(); state == 4 {
		return x*10 + state
	}
	return state
}

func main() {
	ifInitBeforeCondition()
}
