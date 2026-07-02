package main

type blankFieldSelectorStruct struct {
	_ int
	x int
}

func main() {
	var s blankFieldSelectorStruct
	_ = s._
}
