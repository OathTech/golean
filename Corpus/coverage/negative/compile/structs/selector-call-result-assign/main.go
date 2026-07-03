package main

type selectorCallResultAssignStruct struct {
	x int
}

func selectorCallResultAssignValue() selectorCallResultAssignStruct {
	return selectorCallResultAssignStruct{x: 1}
}

func main() {
	selectorCallResultAssignValue().x = 2
}
