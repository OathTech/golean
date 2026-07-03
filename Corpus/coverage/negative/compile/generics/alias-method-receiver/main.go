package main

type aliasSlice[T any] = []T

func (s aliasSlice[int]) sum() int {
	return len(s)
}
