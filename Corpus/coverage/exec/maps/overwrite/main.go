package main

func mapOverwrite() int {
	m := map[string]int{"x": 1}
	m["x"] = 7
	m["y"] = 3
	m["x"] = 9
	return len(m)*100 + m["x"]*10 + m["y"]
}

func main() {
	mapOverwrite()
}
