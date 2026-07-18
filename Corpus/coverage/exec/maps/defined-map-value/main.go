package main

import "fmt"

type Index uint64

type ackMap map[uint64]Index

func definedMapValue() int {
	m := ackMap{}
	m[1] = 5
	m[2] = 9
	v, ok := m[2]
	r := 0
	if ok {
		r = int(v)
	}
	return r + len(m)*10
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", definedMapValue())
}
