// E5 probe: `x, a[i].f = 1, 7/z` (z = 0). Phase 1 must evaluate 7/z
// (division panic). Does gc land the x = 1 store BEFORE that phase-1
// panic? Spec-literal two-phase order (the machine's point) keeps
// x = 0; gc is recorded landing x = 1 early.
package main

type T struct{ f int }

var a = []T{{0}}
var i = 0
var z = 0
var x = 0

func main() {
	defer func() {
		if r := recover(); r != nil {
			println("recovered:", r.(error).Error(), "| x =", x)
		}
	}()
	x, a[i].f = 1, 7/z
	println("unreachable")
}
