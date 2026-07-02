package main

type rangeMapBox struct {
	n int
}

func rangeMapValueCopy() int {
	m := map[int]rangeMapBox{1: {n: 4}, 2: {n: 7}}
	for _, v := range m {
		v.n = 99
	}
	return m[1].n*10 + m[2].n
}
