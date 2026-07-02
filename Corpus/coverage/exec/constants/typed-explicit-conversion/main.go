package main

func typedConstantExplicitConversion() int {
	const k int = 42
	return int(float64(k)) + int(int64(k))
}

func main() {
	typedConstantExplicitConversion()
}
