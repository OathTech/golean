package main

func deferInLoop() (result int) {
	for i := 0; i < 3; i++ {
		defer func(v int) {
			result = result*10 + v
		}(i)
	}
	return 9
}
