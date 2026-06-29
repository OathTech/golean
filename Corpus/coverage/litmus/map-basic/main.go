package main

import "fmt"

func main() {
	var nilMap map[int]int
	nilHit := nilMap[3]
	m := make(map[int]int, 2)
	m[3] = 10
	m[4] = 20
	z := len(nilMap)*10000 + len(m)*1000 + nilHit*100 + m[3]*10 + m[5]

	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
