package main

func closureLoopVarCapture() int {
	total := 0
	adders := 0
	for i := 0; i < 3; i++ {
		f := func() int { return i }
		total = total*10 + f()
		adders = adders + 1
	}
	return total*10 + adders
}

func main() {
	closureLoopVarCapture()
}
