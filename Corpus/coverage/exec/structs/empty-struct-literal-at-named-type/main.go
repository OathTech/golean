package main

// BUG-011 guardrail (owed corpus case, filed 2026-08-04): an anonymous
// `struct{}{}` composite literal is ASSIGNABLE to any defined type whose
// underlying type is struct{} (identical underlying types, one side not a
// defined type). The machine's normalization used raw TypeId identity and
// went stuck. Each subject exercises one assignment context; `reverse` is
// the other assignability direction; `compare` is the mixed-operand
// comparison (one operand assignable to the other's type).

type emptyMarker struct{}

func emptyTakes(m emptyMarker) int {
	_ = m
	return 2
}

func emptyGives() emptyMarker {
	return struct{}{}
}

func emptyStructVarInit() int {
	var m emptyMarker = struct{}{}
	_ = m
	return 1
}

func emptyStructParam() int {
	return emptyTakes(struct{}{})
}

func emptyStructReturn() int {
	m := emptyGives()
	_ = m
	return 3
}

func emptyStructMapStore() int {
	set := map[string]emptyMarker{}
	set["a"] = struct{}{}
	return len(set)
}

func emptyStructReverse() int {
	var u struct{} = emptyMarker{}
	_ = u
	return 5
}

func emptyStructCompare() int {
	var m emptyMarker = struct{}{}
	if m == struct{}{} {
		return 6
	}
	return 0
}
