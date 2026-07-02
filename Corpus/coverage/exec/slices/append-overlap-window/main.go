package main

func appendOverlapWindow() int {
	s := []int{1, 2, 3, 4}
	s = append(s[:1], s[2:]...)
	all := s[:cap(s)]
	return len(s)*100000 + cap(s)*10000 + all[0]*1000 + all[1]*100 + all[2]*10 + all[3]
}
