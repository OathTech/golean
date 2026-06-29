package main

import "fmt"

func main() {
	s := "hé"
	a := s[1]
	b := s[2]
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		a,
		b,
	)
}
