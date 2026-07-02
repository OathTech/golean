package main

func signedWidthWrap() (int, int) {
	var a int8 = -128
	a--
	var b int16 = 32767
	b++
	return int(a), int(b)
}

func main() {
	signedWidthWrap()
}
