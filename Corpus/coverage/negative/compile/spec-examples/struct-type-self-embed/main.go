// spec#Struct_types block Struct_types-6-4cfd4d7d: invalid struct type T1: T1 contains a field of T1
package main

type T1 struct{ T1 } // T1 contains a field of T1

func main() {}
