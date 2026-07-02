package main

func fullSliceCapZero() int {
	base := []int{1, 2, 3}
	window := base[:0:0]
	window = append(window, 9)
	return len(window)*10000 + cap(window)*1000 + window[0]*100 + base[0]*10 + base[1]
}
