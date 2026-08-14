// E4 probe variant: the panicking target moved to the SECOND target
// position (plain b first) — does gc's pick change with position?
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
	b, xs[ys[9]] = zs[7], 2
	println("unreachable")
}
