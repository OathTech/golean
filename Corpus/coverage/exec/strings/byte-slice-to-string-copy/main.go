package main

func byteSliceToStringCopy() (byte, byte) {
	bs := []byte{65, 66}
	s := string(bs)
	bs[0] = 90
	return s[0], bs[0]
}

func main() {
	byteSliceToStringCopy()
}
