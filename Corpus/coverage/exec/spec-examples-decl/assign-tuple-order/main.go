package main

// spec#Assignment_statements block Assignment_statements-7-5f7deaa8: in a
// tuple assignment, first all index expressions and pointer indirections on
// the left are evaluated (in the usual order), then the assignments are
// carried out in left-to-right order. The block asserts each intermediate
// state; the panic rows pin that assignments BEFORE the panicking one have
// already taken effect (observed via recover).

type Point struct{ x, y int }

func exchange() int {
	a, b := 1, 2
	a, b = b, a     // exchange a and b
	return a*10 + b // 21
}

func indexThenVar() int {
	x := []int{1, 2, 3}
	i := 0
	i, x[i] = 1, 2                              // set i = 1, x[0] = 2
	first := i*1000 + x[0]*100 + x[1]*10 + x[2] // 1223
	i = 0
	x[i], i = 2, 1                               // set x[0] = 2, i = 1
	second := i*1000 + x[0]*100 + x[1]*10 + x[2] // 1223
	x[0], x[0] = 1, 2                            // set x[0] = 1, then x[0] = 2 (so x[0] == 2 at end)
	return first + second + x[0]                 // 2448
}

// panicSecondTarget: x[1], x[3] = 4, 5 sets x[1] = 4, THEN panics setting
// x[3]; the recover observes x[1] == 4.
func panicSecondTarget() (out int) {
	x := []int{1, 2, 3}
	defer func() {
		if recover() != nil {
			out = x[1]
		}
	}()
	x[1], x[3] = 4, 5 // set x[1] = 4, then panic setting x[3] = 5
	return -1
}

// panicNilField: x[2], p.x = 6, 7 sets x[2] = 6, then panics setting p.x for
// nil p; the recover observes x[2] == 6.
func panicNilField() (out int) {
	x := []int{1, 2, 3}
	var p *Point
	defer func() {
		if recover() != nil {
			out = x[2]
		}
	}()
	x[2], p.x = 6, 7 // set x[2] = 6, then panic setting p.x = 7
	return -1
}

// rangeAssignForm: for i, x[i] = range x with a break — the block asserts
// i == 0 and x == []int{3, 5, 3} afterwards (x[i] resolves with the OLD i).
func rangeAssignForm() int {
	i := 2
	x := []int{3, 5, 7}
	for i, x[i] = range x { // set i, x[2] = 0, x[0]
		break
	}
	return i*1000 + x[0]*100 + x[1]*10 + x[2] // 353
}
