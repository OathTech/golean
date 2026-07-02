package main

func deferPanicRecoveredAfterReturn() (result int) {
	defer func() {
		if recover() != nil {
			result = result*10 + 1
		}
	}()
	defer func() {
		panic("after return")
	}()
	return 5
}

