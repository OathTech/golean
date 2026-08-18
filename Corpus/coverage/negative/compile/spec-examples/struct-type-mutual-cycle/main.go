// spec#Struct_types block Struct_types-6-4cfd4d7d: invalid struct types T3/T4: mutual containment through array and struct only
package main

type (
	T3 struct{ T4 }       // T3 contains T3 as component of an array in struct T4
	T4 struct{ f [10]T3 } // T4 contains T4 as component of struct T3 in an array
)

func main() {}
