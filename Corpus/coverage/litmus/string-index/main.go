package main

import "fmt"

func stringIndex() (byte, byte) {
	s := "hé"
	a := s[1]
	b := s[2]
	return a, b
}

func main() {
	a, b := stringIndex()
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		a,
		b,
	)
}
