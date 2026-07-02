package main

type mapNilValueRecord struct {
	x int
}

func mapNilReadValueTypes() int {
	var bools map[int]bool
	var strings map[int]string
	var records map[int]mapNilValueRecord
	result := 0
	if bools[1] {
		result += 1000
	}
	result += len(strings[2])*100 + records[3].x
	return result
}
