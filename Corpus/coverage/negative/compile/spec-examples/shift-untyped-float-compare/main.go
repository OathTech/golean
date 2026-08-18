// spec#Operators block Operators-2-7ca475c4: var u1 = 1.0<<s != 0 illegal: 1.0 has type float64, cannot shift
package main

var s uint = 33

var u1 = 1.0<<s != 0 // illegal: 1.0 has type float64, cannot shift

func main() { _ = u1 }
