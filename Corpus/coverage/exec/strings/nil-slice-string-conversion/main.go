package main

func nilSliceStringConversion() int {
	var bs []byte
	var rs []rune
	sb := string(bs)
	sr := string(rs)
	score := len(sb)*100 + len(sr)*10
	if sb == "" {
		score += 1
	}
	if sr == "" {
		score += 2
	}
	return score
}
