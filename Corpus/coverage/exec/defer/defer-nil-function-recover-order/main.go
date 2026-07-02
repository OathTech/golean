package main

func deferNilFunctionRecoverOrder() (result int) {
	var f func()
	defer func() {
		if recover() != nil {
			result = result*10 + 2
		}
	}()
	defer f()
	result = 4
	return
}

