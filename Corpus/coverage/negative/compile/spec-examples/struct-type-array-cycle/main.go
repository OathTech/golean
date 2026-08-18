// spec#Struct_types block Struct_types-6-4cfd4d7d: invalid struct type T2: T2 contains T2 as component of an array
package main

type T2 struct{ f [10]T2 } // T2 contains T2 as component of an array

func main() {}
