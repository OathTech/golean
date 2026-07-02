package main

func breakLabelSelect() int {
	result := 1
outer:
	select {
	default:
		result = result*10 + 2
		break outer
	}
	result = result*10 + 3
	return result
}
