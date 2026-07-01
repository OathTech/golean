package main

type ctr struct {
	n int
}

func mapCopyWrite() int {
	m := map[string]ctr{"a": {n: 1}}
	v := m["a"]
	v.n++
	m["a"] = v
	return m["a"].n
}
