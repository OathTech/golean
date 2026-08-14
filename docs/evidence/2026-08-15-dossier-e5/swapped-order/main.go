// E5 probe variant: RHS positions swapped — `a[i].f, x = 7/z, 1`.
// Does gc still land the x store early when the panicking RHS operand
// precedes x's value lexically?
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
	a[i].f, x = 7/z, 1
	println("unreachable")
}
