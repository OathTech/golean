package main

func continueLabelPost() int {
	result := 0
outer:
	for i := 0; i < 3; i++ {
		result = result*10 + i
		for j := 0; j < 2; j++ {
			continue outer
		}
		result = 99
	}
	return result
}
