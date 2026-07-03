package main

type selectorConversionResultAssignStruct struct {
	x int
}

type selectorConversionResultAssignAlias selectorConversionResultAssignStruct

func main() {
	selectorConversionResultAssignStruct(selectorConversionResultAssignAlias{x: 1}).x = 2
}
