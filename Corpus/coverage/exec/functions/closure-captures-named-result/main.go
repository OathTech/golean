package main

func viaClosure() (result int) {
	set := func(v int) { result = v }
	set(42)
	return
}

func closureCapturesNamedResult() int {
	return viaClosure()
}

func main() {
	closureCapturesNamedResult()
}
