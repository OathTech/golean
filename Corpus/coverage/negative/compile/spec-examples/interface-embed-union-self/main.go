// spec#General_interfaces block General_interfaces-6-42003263: Bad3 may not embed a union containing Bad3
package main

// illegal: Bad3 may not embed a union containing Bad3
type Bad3 interface {
	~int | ~string | Bad3
}

func main() {}
