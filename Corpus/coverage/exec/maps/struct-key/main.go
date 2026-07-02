package main

type mapStructKey struct {
	a int
	b string
}

func mapStructKeyLookup() int {
	m := map[mapStructKey]int{
		{a: 1, b: "x"}: 4,
		{a: 2, b: "y"}: 5,
	}
	return len(m)*100 + m[mapStructKey{a: 1, b: "x"}]*10 + m[mapStructKey{a: 2, b: "y"}]
}

func main() {
	mapStructKeyLookup()
}
