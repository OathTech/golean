package main

func floatToUintTruncation() int {
	a := 12.9
	b := 0.9
	return int(uint8(a))*10 + int(uint8(b))
}
