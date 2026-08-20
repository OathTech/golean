package main

import "fmt"

// H-3 edge: pointer vs value receiver. The quarantined method is declared
// on `*ptrOnly`, so Go's method-set asymmetry says a VALUE `ptrOnly` does
// not satisfy `ptrIface` while `*ptrOnly` does. The stub must carry the
// pointer receiver type verbatim — a stub recorded with the wrong receiver
// would flip one of these two answers silently.

type ptrOnly struct{ n int }

func (p *ptrOnly) bump() int { p.n++; return p.n }

func (p *ptrOnly) render() string { return fmt.Sprint(p.n) }

type ptrIface interface {
	bump() int
	render() string
}

func quarantinePtrValueNotSatisfies() int {
	var x any = ptrOnly{n: 1}
	if _, ok := x.(ptrIface); ok {
		return 1
	}
	return 0
}

func quarantinePtrSatisfies() int {
	var x any = &ptrOnly{n: 1}
	if _, ok := x.(ptrIface); ok {
		return 1
	}
	return 0
}

func quarantinePtrCall() int {
	p := &ptrOnly{n: 1}
	return len(p.render())
}

func main() {
	println(quarantinePtrValueNotSatisfies(), quarantinePtrSatisfies(), quarantinePtrCall())
}
