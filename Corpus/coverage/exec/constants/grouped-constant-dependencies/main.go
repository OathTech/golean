package main

const (
	baseValue      = 3
	doubleBase     = baseValue * 2
	doublePlusIota = doubleBase + iota
)

func groupedConstantDependencies() int {
	return baseValue*100 + doubleBase*10 + doublePlusIota
}
