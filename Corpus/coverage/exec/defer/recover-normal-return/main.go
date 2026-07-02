package main

func recoverNormalReturn() (result int) {
	defer func() {
		if recover() == nil {
			result += 10
		}
	}()
	return 3
}

