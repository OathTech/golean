// spec#Making_slices_maps_and_channels block Making_slices_maps_and_channels-2-3bf764de: make([]int, 10, 0) illegal: constant len must be no larger than constant cap
package main

func main() {
	s := make([]int, 10, 0) // illegal: len(s) > cap(s)
	_ = s
}
