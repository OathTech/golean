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

func main() {
	x := cell{42}
	y := cell{17}

	swap1(&x, &y, 42, 17)
	if !(x == (cell{17}) && y.val == 42) {
		fmt.Println("{\"message\":\"GoCore assertion failed\",\"status\":\"assertion_error\"}")
		return
	}

	swap2(&x, &y)
	if !(x == (cell{42}) && y == (cell{17})) {
		fmt.Println("{\"message\":\"GoCore assertion failed\",\"status\":\"assertion_error\"}")
		return
	}

	(&x).swap3(&y)
	if !(x == (cell{17}) && y == (cell{42})) {
		fmt.Println("{\"message\":\"GoCore assertion failed\",\"status\":\"assertion_error\"}")
		return
	}

	fmt.Println("{\"status\":\"ok\",\"values\":[]}")
}
