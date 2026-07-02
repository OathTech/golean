package main

const dependentA = 3
const dependentB = dependentA + 4
const dependentC = dependentB * dependentA

func dependentConstants() int {
	return dependentC
}
