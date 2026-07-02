package main

func repeatedIndexWrite() int {
	s := []int{0}
	s[0], s[0] = 1, 2
	return s[0]
}

func main() {
	repeatedIndexWrite()
}
