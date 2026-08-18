// spec#General_interfaces block General_interfaces-5-61c674f4: non-basic interfaces may only be used as type constraints, not as variable types
package main

type Float interface {
	~float32 | ~float64
}

var x Float // illegal: Float is not a basic interface

func main() { _ = x }
