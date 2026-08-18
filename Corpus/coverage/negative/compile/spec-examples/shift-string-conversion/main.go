// spec#Operators block Operators-2-7ca475c4: var v2 = string(1<<s) illegal: 1 is converted to a string, cannot shift
package main

var s uint = 33

var v2 = string(1 << s) // illegal: 1 is converted to a string, cannot shift

func main() { _ = v2 }
