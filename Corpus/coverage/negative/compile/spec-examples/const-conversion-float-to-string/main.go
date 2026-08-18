// spec#Conversions block Conversions-3-aa36f537: string(65.0) illegal: 65.0 is not an integer constant
package main

const _ = string(65.0) // illegal: 65.0 is not an integer constant

func main() {}
