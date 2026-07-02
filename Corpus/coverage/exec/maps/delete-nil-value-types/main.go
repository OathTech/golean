package main

type deleteValueStruct struct {
	n int
}

func deleteNilMapValueTypes() int {
	var slices map[string][]int
	var maps map[string]map[int]int
	var structs map[string]deleteValueStruct
	var pointers map[string]*int
	delete(slices, "x")
	delete(maps, "x")
	delete(structs, "x")
	delete(pointers, "x")
	return len(slices)*1000 + len(maps)*100 + len(structs)*10 + len(pointers)
}
