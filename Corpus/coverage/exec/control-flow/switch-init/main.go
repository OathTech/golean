package main

func switchInit() int {
	result := 0
	switch x := 2 + 3; x {
	case 4:
		result = 40
	case 5:
		result = x
	default:
		result = 90
	}
	return result
}

func main() {
	switchInit()
}
