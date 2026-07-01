package main

func deferArgEval() (result int) {
	i := 0
	defer func(captured int) {
		result = captured
	}(i)
	i = 10
	result = i
	return
}
