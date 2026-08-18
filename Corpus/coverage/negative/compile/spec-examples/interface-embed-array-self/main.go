// spec#General_interfaces block General_interfaces-6-42003263: Bad4 may not embed an array containing Bad4 as element type
package main

// illegal: Bad4 may not embed an array containing Bad4 as element type
type Bad4 interface {
	[10]Bad4
}

func main() {}
