package main

type nestedCompareInner struct {
	v any
}

type nestedCompareOuter struct {
	inner nestedCompareInner
}

func interfaceNestedStructComparePanic() int {
	a := nestedCompareOuter{inner: nestedCompareInner{v: []int{1}}}
	b := nestedCompareOuter{inner: nestedCompareInner{v: []int{1}}}
	if a == b {
		return 1
	}
	return 0
}
