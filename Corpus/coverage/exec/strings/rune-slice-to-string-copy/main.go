package main

func runeSliceToStringCopy() int {
	rs := []rune{'é', 'x'}
	s := string(rs)
	rs[0] = 'A'
	fromString := []rune(s)
	return len(s)*10000 + int(fromString[0])*10 + int(rs[0])
}
