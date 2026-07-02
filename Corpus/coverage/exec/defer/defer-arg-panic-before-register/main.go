package main

func deferArgPanicBeforeRegister() (result int) {
	defer func() {
		if recover() != nil {
			result = result*10 + 1
		}
	}()
	zero := 0
	defer func(v int) {
		result = 99
	}(1 / zero)
	return 2
}

