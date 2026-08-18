// spec#Operators block Operators-2-7ca475c4: var u2 = 1<<s != 1.0 illegal: 1 has type float64 (from comparison context), cannot shift
package main

var s uint = 33

var u2 = 1<<s != 1.0 // illegal: 1 has type float64, cannot shift

func main() { _ = u2 }
