package main

import "fmt"

func shifts() (byte, int8) {
	var x byte
	x = 1
	x = x << 8

	var y int8
	y = 0 - 3
	y = y >> 1

	return x, y
}

func main() {
	x, y := shifts()
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		x,
		y,
	)
}
