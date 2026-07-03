package main

type rcCloner[T any] interface {
	Clone() T
}

type rcBox struct {
	n int
}

func (b rcBox) Clone() rcBox {
	return rcBox{n: b.n + 1}
}

func rcCloneTwice[T rcCloner[T]](x T) T {
	return x.Clone().Clone()
}

func recursiveConstraintClone() int {
	return rcCloneTwice(rcBox{n: 5}).n
}

type rcLessSelf[T any] interface {
	Less(T) bool
}

type rcScore int

func (s rcScore) Less(other rcScore) bool {
	return s < other
}

func rcMax[T rcLessSelf[T]](a T, b T) T {
	if a.Less(b) {
		return b
	}
	return a
}

func recursiveConstraintArgumentMethod() int {
	return int(rcMax(rcScore(2), rcScore(9)))
}

type rcLink[T any] interface {
	Next() T
	Value() int
}

type rcNode struct {
	v    int
	next *rcNode
}

func (n *rcNode) Next() *rcNode {
	return n.next
}

func (n *rcNode) Value() int {
	return n.v
}

func rcNextValue[T rcLink[T]](x T) int {
	return x.Next().Value()
}

func recursiveConstraintPointerSelf() int {
	first := &rcNode{v: 1}
	second := &rcNode{v: 7}
	first.next = second
	return rcNextValue(first)
}

type rcComparableCloner[T any] interface {
	comparable
	Clone() T
}

type rcToken int

func (t rcToken) Clone() rcToken {
	return t
}

func rcCloneEqual[T rcComparableCloner[T]](x T) bool {
	return x == x.Clone()
}

func recursiveConstraintComparable() bool {
	return rcCloneEqual(rcToken(3))
}
