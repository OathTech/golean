// spec#Expression_statements block Expression_statements-3-7bc85688: len is not permitted in statement context
package main

func main() {
	len("foo") // illegal if len is the built-in function
}
