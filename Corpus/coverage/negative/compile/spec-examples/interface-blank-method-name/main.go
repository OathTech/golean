// spec#Basic_interfaces block Basic_interfaces-2-c4d2a811: interface method must have a non-blank name
package main

type I interface {
	_(x int) // illegal: method must have non-blank name
}

func main() {}
