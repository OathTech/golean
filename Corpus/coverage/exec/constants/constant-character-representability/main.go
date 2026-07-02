package main

func constantCharacterRepresentability() int {
	const ascii = 'A'
	const latinSmallEAcute = '\u00e9'
	const maxByte = '\xff'
	var b byte = maxByte
	var r rune = latinSmallEAcute
	return int(ascii) + int(b) + int(r)
}
