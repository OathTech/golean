package main

import "fmt"

func main() {
	var x byte
	x = 15
	var y byte
	y = 5
	var zero byte
	zero = 0
	var signedZero int8
	signedZero = 0

	a := x & y
	b := x | y
	c := x ^ y
	d := x &^ y
	e := ^zero
	f := ^signedZero

	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		a,
		b,
		c,
		d,
		e,
		f,
	)
}
