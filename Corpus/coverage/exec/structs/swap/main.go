package main

import "fmt"

type cell struct {
	val int
}

func swap1(x, y *cell, a, b int) {
	x.val, y.val = y.val, x.val
}

func swap2(x, y *cell) {
	x.val, y.val = y.val, x.val
}

func (self *cell) swap3(other *cell) {
	self.val, other.val = other.val, self.val
}

func client() int {
	x := cell{42}
	y := cell{17}

	swap1(&x, &y, 42, 17)
	swap2(&x, &y)
	(&x).swap3(&y)

	return x.val*100 + y.val
}

func main() {
	fmt.Printf("{\"status\":\"ok\",\"values\":[{\"tag\":\"int\",\"value\":%d}]}\n", client())
}
