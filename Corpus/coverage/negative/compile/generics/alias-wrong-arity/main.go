package main

type aliasBox[T any] = struct{ value T }

var _ aliasBox[int, string]
