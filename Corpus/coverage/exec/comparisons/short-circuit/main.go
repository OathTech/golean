package main

type comparisonShortCircuitStruct struct {
	tag     int
	payload any
}

type comparisonShortCircuitNested struct {
	prefix int
	items  [2]any
}

func comparisonArraySkipsInterfacePanic() int {
	a := [2]any{1, []int{1}}
	b := [2]any{2, []int{1}}
	if a == b {
		return 0
	}
	return 1
}

func comparisonArrayReachesInterfacePanic() int {
	a := [2]any{1, []int{1}}
	b := [2]any{1, []int{1}}
	if a == b {
		return 1
	}
	return 0
}

func comparisonStructSkipsInterfacePanic() int {
	a := comparisonShortCircuitStruct{tag: 1, payload: []int{1}}
	b := comparisonShortCircuitStruct{tag: 2, payload: []int{1}}
	if a == b {
		return 0
	}
	return 1
}

func comparisonStructReachesInterfacePanic() int {
	a := comparisonShortCircuitStruct{tag: 1, payload: []int{1}}
	b := comparisonShortCircuitStruct{tag: 1, payload: []int{1}}
	if a == b {
		return 1
	}
	return 0
}

func comparisonNestedArrayStructSkipsPanic() int {
	a := [2]comparisonShortCircuitStruct{
		{tag: 1, payload: 7},
		{tag: 2, payload: []int{1}},
	}
	b := [2]comparisonShortCircuitStruct{
		{tag: 1, payload: 7},
		{tag: 3, payload: []int{1}},
	}
	if a == b {
		return 0
	}
	return 1
}

func comparisonNestedArrayStructReachesPanic() int {
	a := [2]comparisonShortCircuitStruct{
		{tag: 1, payload: 7},
		{tag: 2, payload: []int{1}},
	}
	b := [2]comparisonShortCircuitStruct{
		{tag: 1, payload: 7},
		{tag: 2, payload: []int{1}},
	}
	if a == b {
		return 1
	}
	return 0
}

func comparisonStructNestedArraySkipsPanic() int {
	a := comparisonShortCircuitNested{prefix: 1, items: [2]any{4, []int{1}}}
	b := comparisonShortCircuitNested{prefix: 1, items: [2]any{5, []int{1}}}
	if a == b {
		return 0
	}
	return 1
}

func comparisonStructNestedArrayReachesPanic() int {
	a := comparisonShortCircuitNested{prefix: 1, items: [2]any{4, []int{1}}}
	b := comparisonShortCircuitNested{prefix: 1, items: [2]any{4, []int{1}}}
	if a == b {
		return 1
	}
	return 0
}
