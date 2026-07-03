package main

type selectorCompositeLiteralAddressStruct struct {
	x int
}

func main() {
	_ = &selectorCompositeLiteralAddressStruct{x: 1}.x
}
