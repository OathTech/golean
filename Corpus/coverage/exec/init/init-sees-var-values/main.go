package main

var initSeesBase = 4
var initSeesDerived = initSeesBase + 3
var initSeesResult int

func init() {
	initSeesResult = initSeesBase*10 + initSeesDerived
}

func initSeesVarValues() int {
	return initSeesResult
}

func main() {
	initSeesVarValues()
}
