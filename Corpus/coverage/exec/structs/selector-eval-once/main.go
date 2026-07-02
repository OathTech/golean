package main

type selectorEvalOnceStruct struct {
	x int
}

func structSelectorEvalOnce() int {
	s := &selectorEvalOnceStruct{x: 3}
	calls := 0
	get := func() *selectorEvalOnceStruct {
		calls++
		return s
	}
	get().x += 4
	return calls*100 + s.x
}

func main() {
	structSelectorEvalOnce()
}
