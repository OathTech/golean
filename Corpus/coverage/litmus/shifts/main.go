package main

import "fmt"

func main() {
	var x byte
	x = 1
	x = x << 8

	var y int8
	y = 0 - 3
	y = y >> 1

	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		x,
		y,
	)
}
