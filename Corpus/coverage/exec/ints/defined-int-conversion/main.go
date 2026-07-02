package main

type definedMeters int16
type definedCount int16

func definedIntConversion() int {
	var m definedMeters = 7
	c := definedCount(m)
	return int(c) + int(m)
}

func main() {
	definedIntConversion()
}
