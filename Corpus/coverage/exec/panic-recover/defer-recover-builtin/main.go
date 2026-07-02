package main

func deferRecoverBuiltin() (result int) {
	defer func() {
		result = 7
	}()
	defer recover()
	panic("boom")
}

