package main

func panicIntResult() int {
	panic("return expression")
}

func returnExpressionPanicRecovered() (result int) {
	result = 2
	defer func() {
		if recover() != nil {
			result += 5
		}
	}()
	return panicIntResult()
}

