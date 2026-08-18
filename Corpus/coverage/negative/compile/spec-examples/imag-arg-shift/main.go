// spec#Complex_numbers block Complex_numbers-2-00dfb7ad: imag(3 << s) illegal: 3 assumes complex type, cannot shift
package main

var s int = complex(1, 0) // untyped complex constant 1 + 0i can be converted to int

func main() {
	_ = imag(3 << s) // illegal: 3 assumes complex type, cannot shift
}
