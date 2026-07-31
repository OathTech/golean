package main

import "sort"

// An IMPORTED named type has no TypeDef on the wire (the frontend emits type
// declarations only for the analyzed package), and `tyUncomparable` used to
// classify such an unknown defined type as COMPARABLE — so this insert
// silently succeeded where Go panics (pre-merge audit 2026-07-31, finding 11).
// The machine now fails CLOSED on unknown comparability; this case is a pinned
// RED until imported type declarations reach the wire.

func importedNamedKeyAssign() int {
	m := map[any]int{}
	m[sort.IntSlice{1, 2}] = 1
	return len(m)
}
