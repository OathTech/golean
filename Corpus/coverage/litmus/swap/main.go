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

func client() {
	x := cell{42}
	y := cell{17}

	swap1(&x, &y, 42, 17)
	swap2(&x, &y)
	(&x).swap3(&y)

	_, _ = x, y
}

func main() {
	client()
	fmt.Println("{\"status\":\"ok\",\"values\":[]}")
}
