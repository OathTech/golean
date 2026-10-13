package main

// Fix round 2026-10-13 (review MEDIUM-1, BUG-078 «PER DECLARATION»): the
// idioms that accompany a type with methods — the compile-time interface
// check `var _ Sizer = (*Big)(nil)` and `var p = &Big{}` — over a type
// past the materialization budget are H-11 effect-isolated (a nil
// conversion and an address-of fresh composite literal: no call, no
// panic, no write a reader can see), so they are skipped and poisoned
// per declaration instead of refusing the WHOLE export. The reader of
// `p` is a quarantine stub (RED BY DESIGN, oracle truth `ok`); the
// unrelated subject in the same package PASSes.
type Big [70000]int

type Sizer interface{ Size() int }

func (b *Big) Size() int { return len(b) }

var _ Sizer = (*Big)(nil)

var p = &Big{}

func readP() int { return p.Size() }

func unrelated() int {
	s := 0
	for i := 0; i < 5; i++ {
		s += i * 3
	}
	return s
}

func main() { println(readP(), unrelated()) }
