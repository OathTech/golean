package main

func mark(p *int, n int) int {
	*p = *p*10 + n
	return n
}

func switchCaseCall() int {
	trace := 0
	result := 0
	switch 2 {
	case mark(&trace, 1):
		result = 10
	case mark(&trace, 2):
		result = 20
	case mark(&trace, 3):
		result = 30
	}
	return trace*100 + result
}

func main() {
	switchCaseCall()
}
