package main

func panickingSwitchCaseExpr() int {
	panic("case expression")
}

func switchCaseExpressionPanic() (result int) {
	result = 1
	defer func() {
		if recover() != nil {
			result = result*10 + 2
		}
	}()
	switch 2 {
	case panickingSwitchCaseExpr():
		result = 9
	}
	return result
}

