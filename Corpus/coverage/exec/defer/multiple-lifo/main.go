package main

func deferMultipleLIFO() (result int) {
	defer func() {
		result = result*10 + 2
	}()
	defer func() {
		result = result*10 + 3
	}()
	return 1
}

func main() {
	deferMultipleLIFO()
}
