// spec#Complex_numbers block Complex_numbers-2-00dfb7ad: complex(1, 2<<s) illegal: 2 assumes floating-point type, cannot shift
package main

var s int = complex(1, 0) // untyped complex constant 1 + 0i can be converted to int

func main() {
	_ = complex(1, 2<<s) // illegal: 2 assumes floating-point type, cannot shift
}
