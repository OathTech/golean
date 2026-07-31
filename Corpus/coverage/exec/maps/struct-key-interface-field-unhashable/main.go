package main

// Go's `typehash` is VALUE-directed: it recurses into struct fields, so a
// statically comparable struct key holding an interface field with an
// unhashable dynamic value panics at hash time, naming the INNER type
// (pre-merge audit 2026-07-31, finding 1 — the precheck only matched a key
// that was ITSELF a box, so these silently succeeded).

type hashKey struct{ v any }

func structKeyAssign() int {
	m := map[hashKey]int{}
	m[hashKey{v: []int{1}}] = 1
	return len(m)
}

func structKeyAccessEmpty() int {
	m := map[hashKey]int{}
	return m[hashKey{v: []int{1}}]
}

func structKeyAccessNonEmpty() int {
	m := map[hashKey]int{{v: 3}: 9}
	return m[hashKey{v: []int{1}}]
}

func structKeyDeleteNonEmpty() int {
	m := map[hashKey]int{{v: 3}: 9}
	delete(m, hashKey{v: []int{1}})
	return len(m)
}
