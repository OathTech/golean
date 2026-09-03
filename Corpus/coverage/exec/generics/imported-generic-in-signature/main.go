// FR-23 witness — an imported generic type instantiated in a method
// SIGNATURE (iter.Seq[int], iter.Seq2[string,int] as result types) is
// unstubbable today (quarantinedMethodStub's sigRefusal arm), so the whole
// export refuses even though the subject below never calls the methods.
// Shape lifted from cedar-go types.Record.All / PolicyMap.All (census
// 2026-09-03). Legal Go (1.23 iterators); gc PASS expected.
package main

import "iter"

type Bag struct{ items []int }

// The Go 1.23 iteration-API idiom: iter.Seq / iter.Seq2 result types.
func (b Bag) All() iter.Seq[int] {
	return func(yield func(int) bool) {
		for _, v := range b.items {
			if !yield(v) {
				return
			}
		}
	}
}

func (b Bag) Indexed() iter.Seq2[string, int] {
	return func(yield func(string, int) bool) {
		for _, v := range b.items {
			if !yield("k", v) {
				return
			}
		}
	}
}

func unrelatedToTheIterators() int {
	b := Bag{items: []int{1, 2, 3}}
	return len(b.items)
}

func main() {}
