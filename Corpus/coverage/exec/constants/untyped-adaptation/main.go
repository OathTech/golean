package main

func untypedConstantAdaptation() int {
	const k = 42
	var f float64 = k
	var i int = k
	var b byte = k
	var r rune = k
	return int(f) + i + int(b) + int(r)
}

func main() {
	untypedConstantAdaptation()
}
