// E3 probe: the call-free assignMany twin — same axis without any
// call in the statement (E2's pin is not in play).
package main

var aa = [][]int{{0}, {1}, {2}}
var b = []int{0}
var pn *int

func main() {
	defer func() {
		if r := recover(); r != nil {
			println("recovered:", r.(error).Error())
		}
	}()
	aa[5][0], b[*pn] = 42, 7
	println("unreachable")
}
