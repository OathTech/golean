package main

type selectorUnaddressableLiteralStruct struct {
	x int
}

func main() {
	selectorUnaddressableLiteralStruct{x: 1}.x = 2
}
