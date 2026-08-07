package main

// m[k]++ / m[k]-- with NON-default-int value kinds — BUG-042's map
// facet: emitMapCompound synthesized a default-int 1 for every
// non-float value type, so a map with uint8 (even UNNAMED) or
// defined-type values went stuck at the add ("mismatched + integer
// kinds: uint8 and int"). Float values were fixed by the floats slice
// (F3); these pin the remaining integer kinds through the same site.

type defCount int8

func mapUint8IncDec() int {
	m := map[int]uint8{1: 255, 2: 0}
	m[1]++ // wraps to 0
	m[2]-- // wraps to 255
	return int(m[1])*1000 + int(m[2])
}

func mapDefinedIncDec() int {
	m := map[int]defCount{1: 5}
	m[1]++
	m[1]++
	m[2]-- // absent key: zero value read, dec stores -1
	return int(m[1])*100 + int(m[2])
}

func main() {
	mapUint8IncDec()
	mapDefinedIncDec()
}
