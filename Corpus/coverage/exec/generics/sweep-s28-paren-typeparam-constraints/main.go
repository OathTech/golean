// Defect-neighbourhood campaign, shape S28 (spelling admission; members BUG-136/115, and
// BUG-287 fixed in train 26), lane sweep/s28-s29-spelling-symbols, 2026-11-05
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Parenthesised type-parameter
// constraints `[T (any)]`, `[T (interface{ ~int })]`, a parenthesised constraint on a
// generic FUNCTION (a generic TYPE with `[T (any)]` is gc's array-length parse: the
// negative row typeparam-paren-type-constraint), and an instantiation with a
// parenthesised argument; expected = gc.

package main

type myI int

func gAny[T (any)](x T) T { return x }

func gTilde[T (interface{ ~int })](x T) T { return x + 1 }

type holder[T any] struct{ v T }

func (h holder[T]) get() T { return h.v }

func parenTypeParamConstraints() int {
	a := gAny(3)
	b := gTilde(myI(4))
	c := gTilde[(int)](5)
	h := holder[(string)]{"ab"}
	return a + int(b)*10 + c*100 + len(h.get())*1000 // 2653
}

func main() { println("parenTypeParamConstraints", parenTypeParamConstraints()) }
