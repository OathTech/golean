// spec#Operators block Operators-2-7ca475c4: var v1 float32 = 1<<s illegal: 1 has type float32, cannot shift
package main

var s uint = 33

var v1 float32 = 1 << s // illegal: 1 has type float32, cannot shift

func main() { _ = v1 }
