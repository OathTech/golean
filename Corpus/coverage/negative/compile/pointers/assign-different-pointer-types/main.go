package main

type myInt int

func f() {
	var p *int
	var q *myInt = p
	_ = q
}
