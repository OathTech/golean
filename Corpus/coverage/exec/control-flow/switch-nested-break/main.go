package main

func switchNestedBreak() int {
	trace := 0
	switch 1 {
	case 1:
		switch 2 {
		case 2:
			trace = trace*10 + 2
			break
		}
		trace = trace*10 + 7
	}
	trace = trace*10 + 9
	return trace
}

func main() {
	switchNestedBreak()
}
