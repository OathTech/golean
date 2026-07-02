package main

func multiResultMapValue() (int, bool) {
	m := map[string]int{"x": 7}
	v, ok := m["x"]
	return v, ok
}

func main() {
	multiResultMapValue()
}
