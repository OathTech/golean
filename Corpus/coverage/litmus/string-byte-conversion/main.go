package main

import "fmt"

func stringByteConversion() (int, byte, byte, byte) {
	s := "A\xff\n\u00e9"
	bs := []byte(s)
	bs[0] = 66
	t := string(bs)
	return len(bs), s[0], t[0], t[1]
}

func main() {
	a, b, c, d := stringByteConversion()
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		a,
		b,
		c,
		d,
	)
}
