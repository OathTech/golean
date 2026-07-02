package main

func pair() (int, int) {
	return 1, 2
}

func main() {
	var a, b int
	a, b = pair()+1, 3
}
