package main

func recoverDirect() (result int) {
	defer func() {
		if recover() != nil {
			result = 7
		}
	}()
	panic("boom-direct")
}
