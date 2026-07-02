package main

type deleteKeyStruct struct {
	x int
}

func deleteNilMapKeyTypes() int {
	var byArray map[[2]int]int
	var byStruct map[deleteKeyStruct]int
	var byPointer map[*int]int
	var byChannel map[chan int]int
	var byInterface map[any]int
	var p *int
	var ch chan int
	delete(byArray, [2]int{1, 2})
	delete(byStruct, deleteKeyStruct{x: 3})
	delete(byPointer, p)
	delete(byChannel, ch)
	delete(byInterface, deleteKeyStruct{x: 4})
	return len(byArray) + len(byStruct) + len(byPointer) + len(byChannel) + len(byInterface)
}
