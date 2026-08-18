// spec#General_interfaces block General_interfaces-6-42003263: Bad1 may not embed itself using Bad2
package main

// illegal: Bad1 may not embed itself using Bad2
type Bad1 interface {
	Bad2
}
type Bad2 interface {
	Bad1
}

func main() {}
