package main

import "fmt"

func main() {
	s := "A\xff\n\u00e9"
	bs := []byte(s)
	bs[0] = 66
	t := string(bs)
	fmt.Printf(
		"{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d},{\"tag\":\"int\",\"value\":%d}]}\n",
		len(bs),
		s[0],
		t[0],
		t[1],
	)
}
