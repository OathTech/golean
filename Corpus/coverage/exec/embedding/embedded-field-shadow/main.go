package main

type baseRec struct {
	name int
}

type wrapper struct {
	baseRec
	name int
}

func embeddedFieldShadow() int {
	w := wrapper{}
	w.name = 10
	w.baseRec.name = 3
	return w.name*100 + w.baseRec.name
}
