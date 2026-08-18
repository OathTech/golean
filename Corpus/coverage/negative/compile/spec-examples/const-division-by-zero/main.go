// spec#Constant_expressions block Constant_expressions-4-f8ad9971: the divisor of a constant division must not be zero
package main

const _ = 3.14 / 0.0 // illegal: division by zero

func main() {}
