package main

func stringIntRune() int {
	s := string(rune(65))
	b := string([]byte{72, 105})
	return len(s)*100 + int(s[0]) + len(b)*1000 + int(b[1])
}
