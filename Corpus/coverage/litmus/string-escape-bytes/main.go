package main

import "fmt"

func main() {
	s := "A\xff\n\u00e9"
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		len(s),
		s[0],
		s[1],
		s[2],
		s[3],
		s[4],
	)
}
