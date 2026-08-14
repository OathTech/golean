// E4 probe: a panicking TARGET operand (ys[9], len 3) vs a panicking
// RHS operand (zs[7], len 3) in one assignment — which panic does gc
// report? Machine (phase-1 targets-then-RHS) reports the target's.
package main

var xs = []int{0, 1, 2}
var ys = []int{0, 1, 2}
var zs = []int{0, 1, 2}
var b int

func main() {
	defer func() {
		if r := recover(); r != nil {
			println("recovered:", r.(error).Error())
		}
	}()
	xs[ys[9]], b = zs[7], 2
	println("unreachable")
}
