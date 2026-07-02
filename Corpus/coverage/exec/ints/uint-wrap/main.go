package main

func uintWrap() int {
	var a uint8 = 255
	a++
	var b uint16 = 65535
	b += 2
	return int(a)*10 + int(b)
}

func main() {
	uintWrap()
}
