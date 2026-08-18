// spec#General_interfaces block General_interfaces-4-51fa039a: type sets of all non-interface terms must be pairwise disjoint (~int includes MyInt)
package main

type MyInt int

type C interface {
	~int | MyInt // illegal: the type sets for ~int and MyInt are not disjoint (~int includes MyInt)
}

func main() {}
