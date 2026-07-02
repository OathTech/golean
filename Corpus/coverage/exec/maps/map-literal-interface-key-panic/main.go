package main

func mapLiteralInterfaceKeyPanic() int {
	var k any = []int{1}
	_ = map[any]int{k: 1}
	return 0
}
