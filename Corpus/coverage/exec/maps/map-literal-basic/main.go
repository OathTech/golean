package main

import "fmt"

func mapLiteralBasic() int {
	m := map[int]int{1: 10, 2: 20}
	z := len(m)*100 + m[1] + m[2]

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", mapLiteralBasic())
}
