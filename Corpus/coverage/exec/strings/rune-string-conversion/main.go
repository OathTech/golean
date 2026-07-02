package main

func runeStringConversion() int {
	s := string([]rune{65, 233, 128512})
	return len(s)*1000000 + int(s[0])*10000 + int(s[1])*100 + int(s[3])
}
