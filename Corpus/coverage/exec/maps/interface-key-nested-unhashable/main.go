package main

// The hashability check is VALUE-directed, not TYPE-directed: the key here IS
// an interface box, but its dynamic type (a struct) is statically comparable —
// the unhashable value sits one level down, inside the struct's own interface
// field (pre-merge audit 2026-07-31, finding 1, verifier extension c6).

type nestedKey struct{ v any }

func nestedBoxAssign() int {
	m := map[any]int{}
	var k any = nestedKey{v: []int{1}}
	m[k] = 1
	return len(m)
}

func nestedBoxAccessEmpty() int {
	m := map[any]int{}
	var k any = nestedKey{v: []int{1}}
	return m[k]
}

func nestedArrayBoxAccessNonEmpty() int {
	m := map[any]int{1: 1}
	var k any = [2]any{1, []int{1}}
	return m[k]
}
