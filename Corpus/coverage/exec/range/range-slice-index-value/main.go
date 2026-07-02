package main

func rangeSliceIndexValue() int {
	s := []int{1, 2, 3}
	sum := 0
	for i, v := range s {
		v = v * 10
		s[i] = v
		sum += v
	}
	return sum*1000 + s[0]*100 + s[1]*10 + s[2]
}
