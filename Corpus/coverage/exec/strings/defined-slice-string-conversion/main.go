package main

type definedString string
type definedBytes []byte
type definedRunes []rune

func definedSliceStringConversion() int {
	var s definedString = "hé"
	bs := definedBytes(s)
	rs := definedRunes(s)
	sb := definedString(bs)
	sr := definedString(rs)
	return len(bs)*100000 + len(rs)*10000 + len(sb)*1000 + len(sr)*100 + int(bs[0])
}
