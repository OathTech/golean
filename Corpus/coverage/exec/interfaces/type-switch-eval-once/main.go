package main

func typeSwitchEvalOnce() int {
	calls := 0
	next := func() any {
		calls++
		return int8(3)
	}
	switch next().(type) {
	case int8:
		return calls*10 + 1
	default:
		return 0
	}
}

