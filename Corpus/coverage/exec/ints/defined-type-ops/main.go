package main

type intDefinedA int16
type intDefinedB int16

func intDefinedTypeOps() int {
	var a intDefinedA = 5
	var b intDefinedA = 7
	sum := a + b
	if sum > 10 && sum == 12 {
		return int(sum)
	}
	return 0
}

func main() {
	intDefinedTypeOps()
}
