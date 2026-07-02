package main

type interfaceStorageBox struct {
	n int
}

func interfaceStoresValueCopy() int {
	box := interfaceStorageBox{n: 1}
	var x any = box
	box.n = 9
	return x.(interfaceStorageBox).n
}

func interfaceStoresPointerValue() int {
	box := &interfaceStorageBox{n: 1}
	var x any = box
	box.n = 9
	return x.(*interfaceStorageBox).n
}
