package main

type selectorTargetCell struct {
	x int
}

func selectorTargetRHS(slot **selectorTargetCell, next *selectorTargetCell) int {
	*slot = next
	return 7
}

func selectorTargetBeforeRHS() int {
	a := &selectorTargetCell{x: 1}
	b := &selectorTargetCell{x: 2}
	p := a
	p.x, p = selectorTargetRHS(&p, b), p
	return a.x*100 + b.x*10 + p.x
}

func main() {
	selectorTargetBeforeRHS()
}
