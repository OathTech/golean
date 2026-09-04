package main

import "iter"

type Bag struct{ items []int }

func (b Bag) All() iter.Seq[int] {
	return func(yield func(int) bool) {
		for _, v := range b.items {
			if !yield(v) {
				return
			}
		}
	}
}

func (b Bag) Sum(s iter.Seq[int]) int {
	t := 0
	for v := range s {
		t += v
	}
	return t
}

func Evens(n int) iter.Seq[int] {
	return func(yield func(int) bool) {
		for i := 0; i < n; i += 2 {
			if !yield(i) {
				return
			}
		}
	}
}

type Iterable interface{ All() iter.Seq[int] }

type Outer struct {
	Bag
	tag string
}

type Plain struct{ n int }

func sibling() int { return len(Bag{items: []int{1, 2, 3}}.items) }

func callMethod() int {
	n := 0
	for v := range (Bag{items: []int{1, 2, 3}}).All() {
		n += v
	}
	return n
}

func callFunc() int {
	n := 0
	for v := range Evens(6) {
		n += v
	}
	return n
}

func callParam() int { return Bag{}.Sum(Evens(4)) }

func satisfies() (bool, bool) {
	_, okBag := any(Bag{}).(Iterable)
	_, okPlain := any(Plain{}).(Iterable)
	return okBag, okPlain
}

func satisfiesEmbedded() bool {
	_, ok := any(Outer{tag: "x"}).(Iterable)
	return ok
}

func callPromoted() int {
	n := 0
	for v := range (Outer{Bag: Bag{items: []int{4}}}).All() {
		n += v
	}
	return n
}

func main() {
	a, b := satisfies()
	println(sibling(), callMethod(), callFunc(), callParam(), a, b, satisfiesEmbedded(), callPromoted())
}
