package main

type localInt int

func main() {
	var x localInt = 1
	var y int = x
	_ = y
}
