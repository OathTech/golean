// spec#Variable_declarations block Variable_declarations-3-f13e0b23: nil cannot be used to initialize a variable with no explicit type
package main

var n = nil // illegal

func main() { _ = n }
