package main

type functionHolder struct {
	f func(int) int
}

func compositeFunctionStructCall() int {
	h := functionHolder{f: func(x int) int { return x + 7 }}
	return h.f(5)
}

func compositeFunctionSliceCall() int {
	fs := []func(int) int{
		func(x int) int { return x * 2 },
		nil,
		func(x int) int { return x + 3 },
	}
	score := fs[0](4)*10 + fs[2](4)
	if fs[1] == nil {
		score += 1000
	}
	return score
}

func compositeFunctionMapCall() int {
	fs := map[string]func(int) int{
		"inc": func(x int) int { return x + 1 },
	}
	missing := 0
	if fs["missing"] == nil {
		missing = 100
	}
	return fs["inc"](8) + missing + len(fs)*1000
}

func compositeFunctionStructReassign() int {
	h := functionHolder{f: func(x int) int { return x + 1 }}
	first := h.f(4)
	h.f = func(x int) int { return x * 3 }
	return first*10 + h.f(4)
}

func main() {
	compositeFunctionStructCall()
}
