package main

func stringSliceLowHighPanic() string {
	s := "abc"
	low := 2
	high := 1
	return s[low:high]
}
