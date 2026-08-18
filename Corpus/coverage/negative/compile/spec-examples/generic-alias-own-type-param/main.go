// spec#Alias_declarations block Alias_declarations-4-74451fb2: in an alias declaration the given type cannot be a type parameter declared in the same declaration
package main

type A[P any] = P // illegal: P is a type parameter declared in the declaration of A

func main() {}
