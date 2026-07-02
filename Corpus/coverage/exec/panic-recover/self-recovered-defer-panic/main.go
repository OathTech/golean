package main

func selfRecoveredDeferPanic() (result int) {
	defer func() {
		if recover() != nil {
			result = result*10 + 1
		}
	}()
	defer func() {
		defer func() {
			if recover() != nil {
				result = result*10 + 2
			}
		}()
		panic("inner")
	}()
	panic("outer")
}

