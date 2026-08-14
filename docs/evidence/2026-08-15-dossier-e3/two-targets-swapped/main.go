// E3 probe: two panicking targets — WHICH target's operand panic does
// gc report? Target 1: aa[5] (index out of range, len 3). Target 2:
// *pn (nil deref). Machine (left-to-right) reports target 1's.
package main

var aa = [][]int{{0}, {1}, {2}}
var b = []int{0}
var pn *int

func f6() (int, int) { return 1, 2 }

func main() {
	defer func() {
		if r := recover(); r != nil {
			println("recovered:", r.(error).Error())
		}
	}()
	b[*pn], aa[5][0] = f6()
	println("unreachable")
}
