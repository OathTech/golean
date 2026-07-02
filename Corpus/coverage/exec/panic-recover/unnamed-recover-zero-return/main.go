package main

func unnamedRecoverZeroReturn() int {
	defer func() {
		_ = recover()
	}()
	panic("boom")
}

