package main

func floatCompoundAssign() int {
	var f float32 = 2
	f /= 4
	f += 1.5
	f *= 2
	return int(f * 10)
}

func main() {
	floatCompoundAssign()
}
