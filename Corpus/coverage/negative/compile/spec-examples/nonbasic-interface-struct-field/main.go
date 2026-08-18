// spec#General_interfaces block General_interfaces-5-61c674f4: non-basic interface cannot be a component of a non-interface type (struct field)
package main

type Float interface {
	~float32 | ~float64
}

type Floatish struct {
	f Float // illegal
}

func main() {}
