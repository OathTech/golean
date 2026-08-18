package main

// spec#Constant_declarations block Constant_declarations-2-b9b19c33: typed
// and untyped constant declarations — Pi is a typed float64, zero an untyped
// float, size a typed int64, eof an untyped integer, (a b c) = (3 4 "foo")
// untyped, (u v) typed float32 = (0.0 3.0). Untypedness is observed by
// adapting zero/eof to multiple types; the values are the block's comments.

const Pi float64 = 3.14159265358979323846

const zero = 0.0 // untyped floating-point constant

const (
	size int64 = 1024
	eof        = -1 // untyped integer constant
)

const a, b, c = 3, 4, "foo" // a = 3, b = 4, c = "foo", untyped integer and string constants
const u, v float32 = 0, 3   // u = 0.0, v = 3.0

func constDeclForms() int {
	n := 0
	var pi float64 = Pi
	if pi > 3.141592 && pi < 3.141593 {
		n++
	}
	var z32 float32 = zero // untyped: adapts to float32
	var z64 float64 = zero // ... and float64
	if z32 == 0 && z64 == 0 {
		n++
	}
	if size == 1024 {
		n++
	}
	var eint int = eof // untyped integer: adapts to int
	var e8 int8 = eof  // ... and int8
	if eint == -1 && e8 == -1 {
		n++
	}
	if a == 3 && b == 4 && c == "foo" {
		n++
	}
	if u == 0 && v == 3 {
		n++
	}
	return n // 6
}
