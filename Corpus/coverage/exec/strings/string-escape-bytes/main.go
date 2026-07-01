package main

import "fmt"

func stringEscapeBytes() (int, byte, byte, byte, byte, byte) {
	s := "A\xff\n\u00e9"
	return len(s), s[0], s[1], s[2], s[3], s[4]
}

func main() {
	a, b, c, d, e, f := stringEscapeBytes()
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
