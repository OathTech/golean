package main

func switchEmptyClause() int {
	result := 7
	switch 1 {
	case 1:
	default:
		result = 99
	}
	return result
}

func main() {
	switchEmptyClause()
}
