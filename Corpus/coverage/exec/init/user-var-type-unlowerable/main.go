// FR-24 (2026-09-04), the USER-package half: a package-level var whose
// TYPE does not lower (`sync.Map` — FR-14's family; only Mutex/RWMutex/
// WaitGroup/Once are modeled) is POISONED per declaration instead of
// killing the export: the cell seeds as the `$poisoned` placeholder, every
// reference (read, write, method call, address-of) refuses BY NAME, and the
// declaration keeps its init slot (a zero-valued var has no initializer to
// skip, so $pkginit's order of the healthy initializers is untouched).
// Legal Go; gc PASS on every subject.
package main

import "sync"

var seq []string

func note(s string) int { seq = append(seq, s); return len(seq) }

var a = note("a")
var cache sync.Map
var b = note("b")

func unused() int { return a*10 + b }

func orderKept() int {
	if len(seq) != 2 || seq[0] != "a" || seq[1] != "b" {
		return -1
	}
	return len(seq)
}

func used() int {
	cache.Store(1, 41)
	v, ok := cache.Load(1)
	if !ok {
		return -1
	}
	return v.(int) + 1
}

// keep takes the address as `any` so no LOCAL of type *sync.Map is
// declared: a `p := &cache` would refuse on p's OWN type first (a local of
// an unlowerable type — the same fail-closed answer, but not the var's
// name); this shape reaches the var through globalAddr and names it.
func keep(p any) bool { return p != nil }

func addrOf() int {
	if !keep(&cache) {
		return -1
	}
	return 1
}

func main() { println(unused(), orderKept(), used(), addrOf()) }
