// spec#Constant_expressions block Constant_expressions-6-dc29f1de: uint8(^1) illegal: ^1 uses untyped mask (-2), -2 cannot be represented as a uint8
package main

const _ = uint8(^1) // illegal: same as uint8(-2), -2 cannot be represented as a uint8

func main() {}
