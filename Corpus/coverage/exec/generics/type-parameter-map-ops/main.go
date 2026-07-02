package main

type genericCounts map[string]int

func addCount[M ~map[string]int](m M, key string) int {
	m[key]++
	return len(m)*100 + m[key]
}

func genericTypeParameterMapOps() int {
	m := genericCounts{"a": 1}
	return addCount(m, "a")*10 + addCount(m, "b")
}
