package main

func truncateConversion() (int, int) {
	var wide uint16 = 0x1234
	narrow := uint8(wide)
	var neg int32 = -1
	unsigned := uint16(neg)
	return int(narrow), int(unsigned)
}

func main() {
	truncateConversion()
}
