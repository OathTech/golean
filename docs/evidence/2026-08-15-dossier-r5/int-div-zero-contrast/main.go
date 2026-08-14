// R5 contrast: INTEGER division by zero is a mandated run-time panic
// (§Arithmetic operators) — not latitude.
package main

func main() {
	defer func() { println("recovered:", recover().(error).Error()) }()
	z := 0
	println(1 / z)
}
