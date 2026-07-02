package main

type blankFieldRecord struct {
	_ int
	x int
}

func structBlankField() int {
	r := blankFieldRecord{7, 3}
	return r.x
}
