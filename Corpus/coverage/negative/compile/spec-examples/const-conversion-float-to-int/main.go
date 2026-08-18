// spec#Conversions block Conversions-3-aa36f537: int(1.2) illegal: 1.2 cannot be represented as an int
package main

const _ = int(1.2) // illegal: 1.2 cannot be represented as an int

func main() {}
