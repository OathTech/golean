package main

func uintDecrementWrap() int {
	var x uint8
	x--
	if x == 255 {
		return 1
	}
	return 0
}

func main() {
	uintDecrementWrap()
}
