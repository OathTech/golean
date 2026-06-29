package main

import "fmt"

func main() {
	s := "hé"
	t := s[1:2]
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		len(t),
		t[0],
	)
}
