package main

type ComparableCloner[T any] interface {
	comparable
	Clone() T
}

func use[T ComparableCloner[T]](x T) bool {
	return x == x.Clone()
}

type hasSlice struct {
	xs []int
}

func (h hasSlice) Clone() hasSlice {
	return h
}

var _ = use[hasSlice]
