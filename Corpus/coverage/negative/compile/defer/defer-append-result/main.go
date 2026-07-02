package main

func main() {
	s := []int{}
	defer append(s, 1)
}
