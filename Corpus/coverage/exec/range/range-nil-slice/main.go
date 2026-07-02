package main

func rangeNilSlice() int {
	var s []int
	count := 0
	for range s {
		count++
	}
	return len(s)*10 + count
}
