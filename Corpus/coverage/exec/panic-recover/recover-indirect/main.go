package main

func recoverIndirect() int {
	defer func() {
		func() {
			_ = recover()
		}()
	}()
	panic("boom-indirect")
}
