package main

import "fmt"

// counter is a defined type over uint64 (quorum's `type Index uint64`).
type counter uint64

func (c counter) next() counter { return c + 1 }

func definedIntReceiver() int {
	var c counter = 41
	c = c.next()
	return int(c)
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", definedIntReceiver())
}
