package main

type selectorConversionResultAddressStruct struct {
	x int
}

type selectorConversionResultAddressAlias selectorConversionResultAddressStruct

func main() {
	_ = &selectorConversionResultAddressStruct(selectorConversionResultAddressAlias{x: 1}).x
}
