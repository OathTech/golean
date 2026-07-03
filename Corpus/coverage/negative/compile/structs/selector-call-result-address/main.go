package main

type selectorCallResultAddressStruct struct {
	x int
}

func selectorCallResultAddressValue() selectorCallResultAddressStruct {
	return selectorCallResultAddressStruct{x: 1}
}

func main() {
	_ = &selectorCallResultAddressValue().x
}
