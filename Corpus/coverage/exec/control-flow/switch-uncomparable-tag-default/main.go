package main

func switchUncomparableTagDefault() int {
	switch []int{1} {
	default:
		return 1
	}
}

