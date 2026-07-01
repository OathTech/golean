package main

type vec struct {
	x int
}

func (v vec) val() int {
	return v.x
}

func methodExpression() int {
	f := vec.val
	return f(vec{x: 7})
}
