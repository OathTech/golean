package main

type clearEdgeMap map[string]int
type clearEdgeSlice []int

func builtinClearNilMap() int {
	var m map[string]int
	clear(m)
	return len(m)
}

func builtinClearNilSlice() int {
	var s []int
	clear(s)
	return len(s)*10 + cap(s)
}

func builtinClearDefinedMap() int {
	m := clearEdgeMap{"a": 1, "b": 2}
	clear(m)
	m["c"] = 3
	return len(m)*10 + m["c"]
}

func builtinClearDefinedSlice() int {
	s := clearEdgeSlice{4, 5, 6}
	clear(s)
	return len(s)*100 + cap(s)*10 + s[0] + s[2]
}

func builtinClearSliceAliasVisible() int {
	s := []int{7, 8, 9}
	alias := s
	clear(s[:2])
	return alias[0]*100 + alias[1]*10 + alias[2]
}

func builtinClearArraySlice() int {
	a := [3]int{1, 2, 3}
	clear(a[1:])
	return a[0]*100 + a[1]*10 + a[2]
}

func builtinClearEvalOrder() int {
	trace := 0
	s := []int{1, 2}
	clear(clearMarkSlice(&trace, 4, s))
	return trace*100 + s[0]*10 + s[1]
}

func clearMarkSlice(trace *int, tag int, s []int) []int {
	*trace = *trace*10 + tag
	return s
}

func builtinClearGenericSlice[T ~[]int](s T) int {
	clear(s)
	return len(s)*100 + cap(s)*10 + s[0]
}

func builtinClearGenericSliceSubject() int {
	return builtinClearGenericSlice(clearEdgeSlice{5, 6})
}

func builtinClearGenericMap[M ~map[string]int](m M) int {
	clear(m)
	m["z"] = 9
	return len(m)*10 + m["z"]
}

func builtinClearGenericMapSubject() int {
	return builtinClearGenericMap(clearEdgeMap{"x": 1})
}

func builtinDeleteDefinedMap() int {
	m := clearEdgeMap{"a": 1, "b": 2}
	delete(m, "a")
	_, ok := m["a"]
	if ok {
		return -1
	}
	return len(m)*10 + m["b"]
}

func builtinDeleteGenericMap[M ~map[string]int](m M, k string) int {
	delete(m, k)
	return len(m)
}

func builtinDeleteGenericMapSubject() int {
	return builtinDeleteGenericMap(clearEdgeMap{"a": 1, "b": 2}, "b")
}

func builtinDeleteNilMapEvaluatesKey() int {
	var m map[int]int
	trace := 0
	delete(m, clearMarkKey(&trace, 3, 7))
	return trace*10 + len(m)
}

func clearMarkKey(trace *int, tag int, key int) int {
	*trace = *trace*10 + tag
	return key
}

func builtinDeleteMapExprPanicBeforeKey() {
	trace := 0
	delete(clearPanicMap(), clearMarkKey(&trace, 1, 7))
}

func clearPanicMap() map[int]int {
	panic("delete map expr")
}
