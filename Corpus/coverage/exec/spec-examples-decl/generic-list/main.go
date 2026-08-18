package main

// spec#Type_definitions block Type_definitions-5-2ef7be8d (the generic
// self-referential List[T]) + block Type_definitions-7-df4fe91f (a method on
// the generic type; the elided Len body realized as the obvious recursive
// count).

type List[T any] struct {
	next  *List[T]
	value T
}

// The method Len returns the number of elements in the linked list l.
func (l *List[T]) Len() int {
	if l == nil {
		return 0
	}
	return 1 + l.next.Len()
}

func genericList() int {
	l := &List[string]{value: "a", next: &List[string]{value: "b"}}
	return l.Len()*10 + len(l.next.value) // 21
}
