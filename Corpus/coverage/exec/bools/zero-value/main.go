package main

func boolZeroValue() int {
	var b bool
	if b {
		return 1
	}
	return 2
}

func main() {
	boolZeroValue()
}
