package main

func deferFunctionValueEval() (result int) {
	f := func(dst *int) {
		*dst = 1
	}
	defer f(&result)
	f = func(dst *int) {
		*dst = 9
	}
	return 0
}
