package main

type recursiveNode struct {
	value int
	next  *recursiveNode
}

func structRecursivePointer() int {
	tail := &recursiveNode{value: 2}
	head := &recursiveNode{value: 1, next: tail}
	return head.value*10 + head.next.value
}
