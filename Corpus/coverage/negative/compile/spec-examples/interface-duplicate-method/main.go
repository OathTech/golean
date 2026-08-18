// spec#Basic_interfaces block Basic_interfaces-2-c4d2a811: String not unique: each explicitly specified interface method name must be unique
package main

type I interface {
	String() string
	String() string // illegal: String not unique
}

func main() {}
