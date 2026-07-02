package main

type ambiguousPromotedA struct {
	x int
}

type ambiguousPromotedB struct {
	x int
}

type ambiguousPromotedStruct struct {
	ambiguousPromotedA
	ambiguousPromotedB
}

func main() {
	var s ambiguousPromotedStruct
	_ = s.x
}
