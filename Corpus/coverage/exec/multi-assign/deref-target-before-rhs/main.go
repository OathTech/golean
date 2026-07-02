package main

func derefTargetRHS(slot **int, next *int) int {
	*slot = next
	return 8
}

func derefTargetBeforeRHS() int {
	a := 1
	b := 2
	p := &a
	*p, p = derefTargetRHS(&p, &b), p
	return a*100 + b*10 + *p
}

func main() {
	derefTargetBeforeRHS()
}
