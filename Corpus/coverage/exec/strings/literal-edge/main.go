package main

func interpretedSimpleEscapes() (int, byte, byte, byte, byte, byte) {
	s := "\n\r\t\\\""
	return len(s), s[0], s[1], s[2], s[3], s[4]
}

func interpretedOctalHexEscapes() (int, byte, byte, byte) {
	s := "\000\x00\xff"
	return len(s), s[0], s[1], s[2]
}

func interpretedUnicodeEscapeBytes() (int, byte, byte, byte, byte, byte, byte) {
	s := "\u00e9\U0001F600"
	return len(s), s[0], s[1], s[2], s[3], s[4], s[5]
}

func interpretedNulByte() (int, byte, byte, byte) {
	s := "a\x00b"
	return len(s), s[0], s[1], s[2]
}

func rawMultilineLiteral() (int, byte, byte, byte) {
	s := `a
b`
	return len(s), s[0], s[1], s[2]
}

func rawQuotesAndBackslashes() (int, byte, byte, byte, byte) {
	s := `"\n"`
	return len(s), s[0], s[1], s[2], s[3]
}

func rawEmptyLiteral() int {
	s := ``
	return len(s)
}

func main() {
	interpretedSimpleEscapes()
}
