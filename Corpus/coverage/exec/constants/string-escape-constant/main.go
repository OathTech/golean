package main

func stringEscapeConstant() int {
	const s = "a" + "\x62" + "\u03bb"
	return len(s)*100 + int(s[2])
}
