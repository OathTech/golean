package main

type genericDict[K comparable, V any] map[K]V

func genericMapType() int {
	d := genericDict[string, int]{"a": 2}
	d["b"] = 3
	return len(d)*100 + d["a"]*10 + d["b"]
}

func main() {
	genericMapType()
}
