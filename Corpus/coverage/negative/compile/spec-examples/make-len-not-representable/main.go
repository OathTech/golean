// spec#Making_slices_maps_and_channels block Making_slices_maps_and_channels-2-3bf764de: make([]int, 1<<63) illegal: len(s) is not representable by a value of type int
package main

func main() {
	s := make([]int, 1<<63) // illegal: len(s) is not representable by a value of type int
	_ = s
}
