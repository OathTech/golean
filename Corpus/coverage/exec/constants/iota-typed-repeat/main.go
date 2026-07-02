package main

const (
	one byte = 1 << iota
	two
	four
)

func iotaTypedRepeat() int {
	return int(one)*100 + int(two)*10 + int(four)
}
