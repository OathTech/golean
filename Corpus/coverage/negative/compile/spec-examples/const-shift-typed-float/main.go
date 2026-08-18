// spec#Constant_expressions block Constant_expressions-1-665fef14: const g = float64(2) >> 1 illegal: left operand of a constant shift must be of integer type
package main

const g = float64(2) >> 1 // illegal (float64(2) is a typed floating-point constant)

func main() {}
