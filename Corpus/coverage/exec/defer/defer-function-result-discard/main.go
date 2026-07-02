package main

func deferFunctionResultDiscard() (result int) {
	defer func() int {
		result = 3
		return 99
	}()
	return 1
}

