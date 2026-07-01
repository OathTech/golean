package main

import "fmt"

func breakContinue() int {
	z := 0
	i := 0
	for i < 5 {
		i = i + 1
		if i == 2 {
			continue
		}
		z = z + i
		if i == 4 {
			break
		}
	}
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", breakContinue())
}
