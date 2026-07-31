package main

// Go's TWO hash-panic phrasings are keyed on the map's CURRENT entry count,
// not on insert-vs-access (pre-merge audit 2026-07-31, finding 6; probed
// 2026-07-31): `mapassign` never short-circuits and always says
// `runtime error: hash of unhashable type []int`, while `mapaccess`/`mapdelete`
// take the `mapKeyError` shortcut — `hash of unhashable type: []int` — only
// while `h == nil || h.count == 0`.

func accessEmpty() int {
	m := map[any]int{}
	var k any = []int{1}
	return m[k]
}

func accessNonEmpty() int {
	m := map[any]int{1: 1}
	var k any = []int{1}
	return m[k]
}

func accessEmptied() int {
	m := map[any]int{1: 1}
	delete(m, 1)
	var k any = []int{1}
	return m[k]
}

func deleteEmpty() int {
	m := map[any]int{}
	var k any = []int{1}
	delete(m, k)
	return len(m)
}

func deleteNonEmpty() int {
	m := map[any]int{1: 1}
	var k any = []int{1}
	delete(m, k)
	return len(m)
}

func assignNonEmpty() int {
	m := map[any]int{1: 1}
	var k any = []int{1}
	m[k] = 2
	return len(m)
}

func nilMapAccess() int {
	var m map[any]int
	var k any = []int{1}
	return m[k]
}

func nilMapDelete() int {
	var m map[any]int
	var k any = []int{1}
	delete(m, k)
	return len(m)
}
