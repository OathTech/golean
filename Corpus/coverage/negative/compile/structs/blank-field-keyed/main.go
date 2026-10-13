package main

// A keyed struct literal cannot name a blank field (gc and go/types:
// «unknown field _ in struct literal»); BUG-127's negative row.

type blankKeyedS struct {
	_ int
	X int
}

func main() {
	s := blankKeyedS{_: 1, X: 2}
	println(s.X)
}
