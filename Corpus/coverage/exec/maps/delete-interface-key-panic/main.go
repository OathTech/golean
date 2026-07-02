package main

func deleteInterfaceKeyPanic() int {
	m := map[any]int{}
	delete(m, []int{1})
	return len(m)
}
