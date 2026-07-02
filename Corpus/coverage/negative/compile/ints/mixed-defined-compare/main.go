package main

type compareMeters int
type compareFeet int

func main() {
	var m compareMeters = 1
	var f compareFeet = 1
	_ = m == f
}
