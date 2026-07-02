package main

func bad() (err error) {
	if true {
		err := 1
		_ = err
		return
	}
	return
}
