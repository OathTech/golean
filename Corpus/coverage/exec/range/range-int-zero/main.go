package main

func rangeIntZero() int {
	count := 0
	for range 0 {
		count++
	}
	return count
}
