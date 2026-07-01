package main

const huge = 1 << 100
const back = huge >> 100

func constPrecision() int {
	return back
}
