// spec#Array_types block Array_types-3-e776b27a: invalid array type T2: T2 contains T2 as component of a struct
package main

type T2 [10]struct{ f T2 } // T2 contains T2 as component of a struct

func main() {}
