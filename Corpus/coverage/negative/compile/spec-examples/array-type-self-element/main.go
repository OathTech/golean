// spec#Array_types block Array_types-3-e776b27a: invalid array type T1: element type of T1 is T1 (array/struct-only containment)
package main

type T1 [10]T1 // element type of T1 is T1

func main() {}
