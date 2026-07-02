package main

func panicDeferOrder() (result int) {
	defer func() {
		if recover() != nil {
			result = result*10 + 1
		}
	}()
	defer func() {
		result = result*10 + 2
	}()
	panic("boom")
}

func main() {
	panicDeferOrder()
}
