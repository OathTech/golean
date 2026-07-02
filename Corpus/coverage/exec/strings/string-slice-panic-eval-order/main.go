package main

func stringSlicePanicEvalOrder() (result int) {
	s := "abc"
	hi := 2
	defer func() {
		if recover() != nil {
			result = hi
		}
	}()
	hi = 5
	_ = s[:hi]
	return -1
}
