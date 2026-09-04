package main

import "iter"

// FR-4 × FR-23 (2026-09-04, lane fr4-rowm): a method STENCIL whose
// refusal is in its SIGNATURE — `All() iter.Seq[T]` at T = int instantiates
// an imported generic, which no body may produce (FR-23, enqueueTypeInst)
// — must compose with the stencil quarantine: the body emission refuses,
// the stub's signature emits in SIGNATURE-OPAQUE mode (emit.go
// withOpaqueSigs; iter.Seq[int] becomes the opaque marker of FR-23), and
// the export survives per declaration. This is cedar-go's exact kill shape
// (census §10.2: `mapset.ImmutableMapSet[EntityUID].All`, 25 of 34 cases).
//
//   sibling   set[int].size lowers beside the stubbed All (green)
//   satisfies satisfaction THROUGH the opaque key: set[int] has
//             All() iter.Seq[int] (green — the stub carries the real
//             signature)
//   call      All() is called and ranged over — refuses by name; when FR-23
//             / FR-12 land, this row flips (the stencil's body is a plain
//             closure) and must be retargeted, never let go green

type set[T comparable] struct{ items []T }

func (s set[T]) size() int { return len(s.items) }

func (s set[T]) All() iter.Seq[T] {
	return func(yield func(T) bool) {
		for _, v := range s.items {
			if !yield(v) {
				return
			}
		}
	}
}

type iterable interface{ All() iter.Seq[int] }

func sibling() int { return set[int]{items: []int{1, 2, 3}}.size() }

func satisfies() int {
	var x any = set[int]{items: []int{1}}
	if _, ok := x.(iterable); ok {
		return 1
	}
	return 0
}

func call() int {
	n := 0
	for v := range (set[int]{items: []int{1, 2, 3}}).All() {
		n += v
	}
	return n
}

func main() {
	println(sibling())
	println(satisfies())
}
