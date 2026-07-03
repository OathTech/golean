package main

func genericComparableRuntimeEq[T comparable](a T, b T) bool {
	return a == b
}

type genericComparableRuntimeBox struct {
	tag int
	v   any
}

func genericComparableAnyEqualInts() int {
	var a any = 12
	var b any = 12
	if genericComparableRuntimeEq[any](a, b) {
		return 1
	}
	return 0
}

func genericComparableAnyDifferentDynamicTypes() int {
	var a any = 12
	var b any = "12"
	if genericComparableRuntimeEq[any](a, b) {
		return 0
	}
	return 1
}

func genericComparableAnySlicePanic() bool {
	var a any = []int{1}
	var b any = []int{1}
	return genericComparableRuntimeEq[any](a, b)
}

func genericComparableAnyMapPanic() bool {
	var a any = map[string]int{"x": 1}
	var b any = map[string]int{"x": 1}
	return genericComparableRuntimeEq[any](a, b)
}

func genericComparableAnyFuncPanic() bool {
	f := func() {}
	g := func() {}
	var a any = f
	var b any = g
	return genericComparableRuntimeEq[any](a, b)
}

func genericComparableArrayInterfacePanic() bool {
	a := [1]any{[]int{1}}
	b := [1]any{[]int{1}}
	return genericComparableRuntimeEq[[1]any](a, b)
}

func genericComparableStructInterfacePanic() bool {
	a := genericComparableRuntimeBox{tag: 1, v: []int{1}}
	b := genericComparableRuntimeBox{tag: 1, v: []int{1}}
	return genericComparableRuntimeEq[genericComparableRuntimeBox](a, b)
}

func genericComparableStructSkipsInterfacePanic() int {
	a := genericComparableRuntimeBox{tag: 1, v: []int{1}}
	b := genericComparableRuntimeBox{tag: 2, v: []int{1}}
	if genericComparableRuntimeEq[genericComparableRuntimeBox](a, b) {
		return 0
	}
	return 1
}
