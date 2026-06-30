package main

func negativeShift() {
	s := 0 - 1
	_ = 1 << s
}

func main() {
	negativeShift()
}
