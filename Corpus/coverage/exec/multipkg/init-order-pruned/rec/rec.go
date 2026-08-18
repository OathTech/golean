package rec

// rec has NO package-scope variable initializers and NO init function,
// so it has no initialization work of its own and gc emits no
// inittask for it: rec is not a node of the schedule.

// S accumulates one decimal digit per event on the STATIC chain.
var S int

// D accumulates one decimal digit per event on the DYNAMIC chain.
var D int

// PushS records an event on the static chain.
func PushS(mark int) int {
	S = S*10 + mark
	return S
}

// PushD records an event on the dynamic chain.
func PushD(mark int) int {
	D = D*10 + mark
	return D
}
