package main

func floatToIntTruncation() int {
	pos := 2.9
	neg := -2.9
	return int(pos)*10 + int(neg)
}

func main() {
	floatToIntTruncation()
}
