package main

type aliasSet[T comparable] = map[T]bool

var _ aliasSet[[]int]
