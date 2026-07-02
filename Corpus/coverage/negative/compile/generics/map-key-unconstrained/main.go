package main

func badGenericMap[K any](k K) map[K]int {
	return map[K]int{k: 1}
}
