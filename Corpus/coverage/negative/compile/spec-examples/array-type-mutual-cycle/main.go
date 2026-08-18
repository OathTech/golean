// spec#Array_types block Array_types-3-e776b27a: invalid array types T3/T4: T3 contains T3 via struct T4, only array/struct containment
package main

type (
	T3 [10]T4         // T3 contains T3 as component of a struct in T4
	T4 struct{ f T3 } // T4 contains T4 as component of array T3 in a struct
)

func main() {}
