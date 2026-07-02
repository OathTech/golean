package main

func namedPairWithDefer() (a int, b int) {
	a = 2
	b = 5
	defer func() {
		a = a + 10
		b = b * 3
	}()
	return
}

func namedMultiDefer() int {
	a, b := namedPairWithDefer()
	return a*100 + b
}
