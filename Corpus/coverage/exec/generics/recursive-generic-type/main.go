package main

type genericNode[T any] struct {
	value T
	next  *genericNode[T]
}

func genericRecursiveType() int {
	tail := &genericNode[int]{value: 3}
	head := genericNode[int]{value: 2, next: tail}
	return head.value*10 + head.next.value
}
