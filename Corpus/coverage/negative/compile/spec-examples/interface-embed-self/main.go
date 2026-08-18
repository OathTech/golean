// spec#General_interfaces block General_interfaces-6-42003263: Bad may not embed itself
package main

// illegal: Bad may not embed itself
type Bad interface {
	Bad
}

func main() {}
