package main

func signedUnsignedConversion() (int, int) {
	var u uint8 = 255
	i := int8(u)
	back := uint8(i)
	return int(i), int(back)
}

func main() {
	signedUnsignedConversion()
}
