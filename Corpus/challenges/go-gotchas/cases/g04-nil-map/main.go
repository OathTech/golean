package main

import "fmt"

func main() {
	var z int
	var m map[string]int
	z = z + m["x"]
	func() {
		defer func() {
			if recover() != nil {
				z = z + 1
			}
		}()
		m["x"] = 1
	}()
	fmt.Printf("{\"case\":\"g04-nil-map\",\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
