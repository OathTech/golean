package main

// DC01 neighbourhood: a struct's address and its first field's address
// are the same machine word in gc but DIFFERENT TYPES, so Go compares them
// only as interface values, where the dynamic-type rule answers false
// (`*holder` vs `*int`); likewise an array and its first element. The
// machine keeps that rule (interface equality checks the dynamic type
// before any payload comparison) — these are must-stay-false controls for
// the canonical-location fix.

type holder struct {
	X int
	Y int
}

func structVsFirstField() bool {
	a := holder{X: 1}
	return any(&a) == any(&a.X)
}

func structVsItself() bool {
	a := holder{X: 1}
	return any(&a) == any(&a)
}

func arrayVsFirstElem() bool {
	var arr [2]int
	return any(&arr) == any(&arr[0])
}

func main() { println(structVsFirstField(), structVsItself(), arrayVsFirstElem()) }
