package main

func switchClauseScope() int {
	result := 0
	switch 2 {
	case 1:
		x := 10
		result = x
	case 2:
		x := 20
		result = x
	default:
		x := 30
		result = x
	}
	return result
}

func main() {
	switchClauseScope()
}
