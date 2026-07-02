package main

func mapInterfaceSliceKeyPanic() int {
	m := map[any]int{}
	key := any([]int{1})
	return m[key]
}

func main() {
	mapInterfaceSliceKeyPanic()
}
