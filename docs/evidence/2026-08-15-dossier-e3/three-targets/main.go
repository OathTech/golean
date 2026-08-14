// E3 probe: THREE panicking targets — gc's pick is neither first nor
// last (recorded: the middle, [9] with length 3).
package main

var aa = [][]int{{0}, {1}, {2}}
var cc = [][]int{{0}, {1}, {2}}
var dd = [][]int{{0}, {1}, {2}}

func f8() (int, int, int) { return 1, 2, 3 }

func main() {
	defer func() {
		if r := recover(); r != nil {
			println("recovered:", r.(error).Error())
		}
	}()
	aa[5][0], cc[9][0], dd[7][0] = f8()
	println("unreachable")
}
