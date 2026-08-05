package main

var (
	specDepA = specDepC + specDepB
	specDepB = specDepF()
	specDepC = specDepF()
	specDepD = 3
)

func specDepF() int {
	specDepD++
	return specDepD
}

func specDependencyExample() int {
	return ((specDepD*10+specDepC)*10+specDepB)*100 + specDepA
}

func main() {
	specDependencyExample()
}
