package main

func runeSliceConversion() int {
	s := string([]byte{104, 195, 169, 255})
	rs := []rune(s)
	return len(rs)*1000000 + int(rs[0])*10000 + int(rs[1])*100 + int(rs[2])
}
