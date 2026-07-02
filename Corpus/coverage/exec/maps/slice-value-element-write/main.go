package main

func mapSliceValueElementWrite() int {
	m := map[string][]int{"a": {1, 2, 3}}
	m["a"][1] = 9
	return m["a"][0]*100 + m["a"][1]*10 + m["a"][2]
}
