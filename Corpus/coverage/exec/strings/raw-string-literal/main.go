package main

func rawStringLiteral() (int, byte, byte) {
	raw := `a\nb`
	interpreted := "a\nb"
	return len(raw)*10 + len(interpreted), raw[1], interpreted[1]
}

func main() {
	rawStringLiteral()
}
