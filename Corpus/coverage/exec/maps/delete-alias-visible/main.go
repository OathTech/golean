package main

func deleteAliasVisible() int {
	m := map[string]int{"x": 1, "y": 2}
	alias := m
	delete(alias, "x")
	_, okX := m["x"]
	y := m["y"]
	if okX {
		return 100 + y
	}
	return len(m)*10 + y
}
