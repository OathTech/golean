package main

// Promotion through an embedded POINTER field: a non-nil path dispatches
// (call), a nil path panics at the receiver adjustment's implicit deref —
// and that panic happens when the method OPERAND is evaluated, BEFORE the
// call's arguments (before-args pins the evaluation order: calls stays 0).

type nilRecvInner struct {
	n int
}

func (v nilRecvInner) val() int {
	return v.n
}

func (v nilRecvInner) valArg(x int) int {
	return v.n + x
}

type nilRecvOuter struct {
	*nilRecvInner
}

func promotedThroughPointerCall() int {
	o := nilRecvOuter{nilRecvInner: &nilRecvInner{n: 4}}
	return o.val()
}

func promotedNilEmbeddedCallPanics() int {
	var o nilRecvOuter
	return o.val()
}

func promotedNilEmbeddedBeforeArgs() (r int) {
	calls := 0
	defer func() {
		if recover() != nil {
			r = calls*10 + 1
		}
	}()
	var o nilRecvOuter
	bump := func() int {
		calls++
		return 0
	}
	return o.valArg(bump())
}
