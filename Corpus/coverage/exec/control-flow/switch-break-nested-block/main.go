package main

func switchBreakNestedBlock() int {
	trace := 0
	switch 1 {
	case 1:
		trace = trace*10 + 1
		{
			{
				break
			}
		}
	case 2:
		trace = trace*10 + 2
	}
	trace = trace*10 + 5
	return trace
}

func main() {
	switchBreakNestedBlock()
}
