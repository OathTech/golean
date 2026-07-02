package main

func switchMultiCaseValues() int {
	x := 3
	switch x {
	case 1, 2:
		return 12
	case 3, 4, 5:
		return 345
	default:
		return 0
	}
}

func main() {
	switchMultiCaseValues()
}
