// spec#General_interfaces block General_interfaces-2-46b76d35: ~error illegal: in ~T, T cannot be an interface
package main

type C interface {
	~error // illegal: error is an interface
}

func main() {}
