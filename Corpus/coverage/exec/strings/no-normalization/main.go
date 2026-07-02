package main

func noStringNormalization() int {
	composed := "\u00e9"
	decomposed := "e\u0301"
	eq := 0
	if composed == decomposed {
		eq = 1
	}
	return len(composed)*1000 + len(decomposed)*100 + int(composed[0])*10 + eq
}
