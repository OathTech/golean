package main

func stringToRuneCopy() (int, int) {
	s := "\u00e9x"
	rs := []rune(s)
	rs[0] = 'A'
	return int([]rune(s)[0]), int(rs[0])
}

func main() {
	stringToRuneCopy()
}
