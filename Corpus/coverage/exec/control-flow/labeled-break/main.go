package main

func labeledBreak() int {
	plainBreaks := 0
	for n := 0; n < 3; n++ {
		switch {
		case true:
			plainBreaks++
			break
		}
	}
	labeledIter := 0
loop:
	for {
		switch {
		case true:
			break loop
		}
		labeledIter++
	}
	return plainBreaks*10 + labeledIter
}
