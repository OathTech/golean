// spec#Short_variable_declarations block Short_variable_declarations-4-c0320034: x repeated on left side of := (non-blank names must be unique)
package main

func main() {
	x, y, x := 1, 2, 3 // illegal: x repeated on left side of :=
	_, _ = x, y
}
