package main

func recoverTwice() (result int) {
	defer func() {
		if recover() != nil {
			result += 1
		}
		if recover() == nil {
			result += 10
		}
	}()
	panic("twice")
}
