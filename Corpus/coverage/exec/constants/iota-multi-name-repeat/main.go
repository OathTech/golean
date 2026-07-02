package main

const (
	first, firstOffset = iota, iota + 10
	second, secondOffset
	third = iota
	fourth
)

func iotaMultiNameRepeat() int {
	return first*100000 + firstOffset*10000 + second*1000 + secondOffset*100 + third*10 + fourth
}
