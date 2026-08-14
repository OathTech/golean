// E5 probe (the recorded shape, LOCAL variables): `x, a[i].f = 1, 7/z`
// with z = 0 and x a local read by the deferred recover closure.
// gc lands the x = 1 store BEFORE the phase-1 division panic.
package main

type T struct{ f int }

func main() {
	a := []T{{0}}
	i := 0
	z := 0
	x := 0
	defer func() {
		if r := recover(); r != nil {
			println("recovered:", r.(error).Error(), "| x =", x)
		}
	}()
	x, a[i].f = 1, 7/z
	println("unreachable")
}
