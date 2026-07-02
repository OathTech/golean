package main

type interfaceFieldStruct struct {
	v any
}

func structInterfaceFieldComparePanic() {
	a := interfaceFieldStruct{v: []int{1}}
	b := interfaceFieldStruct{v: []int{1}}
	_ = a == b
}

func main() {
	structInterfaceFieldComparePanic()
}
