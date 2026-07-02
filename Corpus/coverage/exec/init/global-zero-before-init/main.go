package main

var globalZeroBeforeInitX int
var globalZeroBeforeInitSeen int

func init() {
	globalZeroBeforeInitSeen = globalZeroBeforeInitX
	globalZeroBeforeInitX = 9
}

func globalZeroBeforeInit() int {
	return globalZeroBeforeInitSeen*10 + globalZeroBeforeInitX
}

func main() {
	globalZeroBeforeInit()
}
