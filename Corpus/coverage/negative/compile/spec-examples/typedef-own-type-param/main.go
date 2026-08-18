// spec#Type_definitions block Type_definitions-6-92a5f453: in a type definition the given type cannot be a type parameter (own list)
package main

type T[P any] P // illegal: P is a type parameter

func main() {}
