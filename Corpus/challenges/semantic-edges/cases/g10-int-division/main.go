package main

import "fmt"

func main() {
	var x int8 = 127
	x++
	z := (-7/2)*1000 + (-7%2)*100 + int(x)
	fmt.Printf("{\"case\":\"g10-int-division\",\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", z)
}
