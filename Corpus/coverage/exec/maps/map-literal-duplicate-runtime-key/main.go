package main

func mapLiteralDuplicateRuntimeKey() int {
	k := 1
	m := map[int]int{
		k: 10,
		k: 20,
	}
	return len(m)*100 + m[1]
}
