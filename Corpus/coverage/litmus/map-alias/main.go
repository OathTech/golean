package main

import "fmt"

func mapAlias() int {
	m := make(map[int]int)
	alias := m
	m[1] = 3
	alias[1] = 7
	z := len(m)*1000 + len(alias)*100 + m[1]*10 + alias[1]

	return z
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", mapAlias())
}
