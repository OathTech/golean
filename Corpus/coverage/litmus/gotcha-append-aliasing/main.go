package main

import "fmt"

func gotchaAppendAliasing() int {
	a := []int{1, 2, 3}
	b := a[:2]
	b = append(b, 99)
	z := a[0]*100000 + a[1]*10000 + a[2]*1000 +
		b[0]*100 + b[1]*10 + b[2]
	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", gotchaAppendAliasing())
}
