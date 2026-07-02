package main

func deferNamedResultLIFO() (result int) {
	defer func() {
		result = result*10 + 1
	}()
	defer func() {
		result = result*10 + 2
	}()
	return 3
}

func main() {
	deferNamedResultLIFO()
}
