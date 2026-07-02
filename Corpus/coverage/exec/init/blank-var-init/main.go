package main

var blankVarTrace int

func blankVarStep(x int) int {
	blankVarTrace = blankVarTrace*10 + x
	return x
}

var _ = blankVarStep(3)
var blankVarValue = blankVarStep(4)

func blankVarInit() int {
	return blankVarTrace*10 + blankVarValue
}

func main() {
	blankVarInit()
}
