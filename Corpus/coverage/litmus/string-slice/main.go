package main

import "fmt"

func stringSlice() (int, byte) {
	s := "hé"
	t := s[1:2]
	return len(t), t[0]
}

func main() {
	n, b := stringSlice()
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		n,
		b,
	)
}
