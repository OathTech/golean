package main

func deleteNilMap() int {
	var m map[string]int
	delete(m, "missing")
	return len(m)
}
