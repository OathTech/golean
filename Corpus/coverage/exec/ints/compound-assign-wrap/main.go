package main

func intCompoundAssignWrap() int {
	var x int8 = 120
	x += 10
	var y uint8 = 3
	y -= 5
	return int(x)*1000 + int(y)
}

func main() {
	intCompoundAssignWrap()
}
