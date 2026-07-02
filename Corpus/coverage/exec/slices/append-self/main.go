package main

func appendSelf() int {
	s := make([]int, 3, 6)
	s[0] = 1
	s[1] = 2
	s[2] = 3
	s = append(s, s...)
	return len(s)*10000000 + cap(s)*1000000 + s[0]*100000 + s[1]*10000 + s[2]*1000 + s[3]*100 + s[4]*10 + s[5]
}
