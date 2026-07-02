package main

type anonymousInner struct {
	n int
}

type anonymousOuter struct {
	anonymousInner
	m int
}

func structAnonymousField() int {
	o := anonymousOuter{anonymousInner: anonymousInner{n: 3}, m: 4}
	o.n = 5
	return o.anonymousInner.n*10 + o.m
}

func main() {
	structAnonymousField()
}
