package main

func deferNamedReturn() (result int) {
	defer func() {
		result++
	}()
	return 5
}
