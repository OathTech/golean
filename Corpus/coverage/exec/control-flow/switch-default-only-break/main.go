package main

func switchDefaultOnlyBreak() int {
	trace := 0
	switch 42 {
	default:
		trace = trace*10 + 4
		if trace > 0 {
			break
		}
		trace = trace*10 + 9
	}
	return trace*10 + 1
}

func main() {
	switchDefaultOnlyBreak()
}
