package main

func deleteNilInterfaceKeyPanic() int {
	var m map[any]int
	delete(m, []int{1})
	return len(m)
}
