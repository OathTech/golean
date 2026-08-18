// spec#General_interfaces block General_interfaces-5-61c674f4: non-basic interface cannot be the type of a value (conversion Float(nil) illegal)
package main

type Float interface {
	~float32 | ~float64
}

var x interface{} = Float(nil) // illegal

func main() { _ = x }
