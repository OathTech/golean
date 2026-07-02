package main

func namedResultPreservedAfterRecover() (result int) {
	result = 6
	defer func() {
		if recover() != nil {
			result++
		}
	}()
	panic("boom")
}

