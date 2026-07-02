package main

func nestedLabeledBreak() int {
	result := 0
outer:
	for i := 0; i < 3; i++ {
		result = result*10 + i + 1
	inner:
		for j := 0; j < 3; j++ {
			result = result*10 + j + 1
			break inner
		}
		if i == 1 {
			break outer
		}
	}
	return result
}
