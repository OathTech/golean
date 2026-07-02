package main

func mapInterfaceKey() int {
	m := map[any]int{
		1:   10,
		"1": 20,
	}
	return len(m)*100 + m[1] + m["1"]
}

func main() {
	mapInterfaceKey()
}
