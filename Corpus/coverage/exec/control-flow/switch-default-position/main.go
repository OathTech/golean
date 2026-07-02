package main

func switchDefaultPosition() int {
	switch 3 {
	default:
		return 1
	case 3:
		return 2
	}
}

func main() {
	switchDefaultPosition()
}
