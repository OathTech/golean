package main

func labeledBreakDefer() (result int) {
	defer func() {
		result += 100
	}()
	result = 1
outer:
	for i := 0; i < 3; i++ {
		for j := 0; j < 3; j++ {
			result++
			if i+j == 1 {
				break outer
			}
		}
	}
	return
}
