package main

import "fmt"

type triple [3]uint64

func (t triple) sum() uint64 { return t[0] + t[1] + t[2] }

func definedArrayReceiver() int {
	t := triple{10, 20, 12}
	return int(t.sum())
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", definedArrayReceiver())
}
