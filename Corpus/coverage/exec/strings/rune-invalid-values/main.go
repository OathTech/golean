package main

func runeInvalidValues() int {
	s := string([]rune{65, -1, 0xD800, 0x110000})
	return len(s)*100000000 + int(s[0])*1000000 + int(s[1])*10000 + int(s[4])*100 + int(s[7])
}
