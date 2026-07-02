package main

func deferRegisteredDuringUnwind() (result int) {
	defer func() {
		if recover() != nil {
			result = result*10 + 1
		}
	}()
	defer func() {
		defer func() {
			result = result*10 + 2
		}()
		result = result*10 + 3
	}()
	panic("boom")
}

