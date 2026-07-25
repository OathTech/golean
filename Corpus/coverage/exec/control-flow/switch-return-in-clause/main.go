package main

func switchReturnInClause() int {
	for i := 0; i < 5; i++ {
		switch i {
		case 2:
			return i * 11
		default:
			continue
		}
	}
	return 999
}

func main() {
	switchReturnInClause()
}
