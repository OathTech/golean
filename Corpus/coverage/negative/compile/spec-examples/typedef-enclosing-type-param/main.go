// spec#Type_definitions block Type_definitions-6-92a5f453: in a type definition the given type cannot be a type parameter of the enclosing function
package main

func f[P any]() {
	type L P // illegal: P is a type parameter declared by the enclosing function
	_ = f[int]
}

func main() {}
